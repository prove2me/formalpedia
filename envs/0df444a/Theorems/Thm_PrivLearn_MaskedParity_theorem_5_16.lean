-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_theorem_5_16
-- name    : PrivLearn.MaskedParity.theorem_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:48:15.13098+00:00
-- url     : https://prove2.me/theorems/8393c162-aebf-4235-b966-3da873b45fcf
-- title:
--   Theorem 5.16 — MASKED-PARITY is learnable by an adaptive but not by a nonadaptive SQ learner under the uniform distribution
-- statement:
--   Let $d$ be a power of two and let the examples be drawn from the uniform distribution on $D=\{0,1\}^d\times\{0,1\}^{\log d}\times\{0,1\}$.
--
--   1. **An adaptive SQ learner learns MASKED-PARITY.** There is a two-round SQ learner, with $d$ queries in the first round and one in the second, all with values in $\{0,1\}$ and tolerance at least $\frac1{4d+1}$, that outputs the target concept $c_{r,a}$ itself for every target and for every valid answers of the SQ oracle.
--   2. **No nonadaptive SQ learner does.** There is an SQ oracle $\mathcal O$ (the oracle of §5.3.2), valid for every target, every query and every tolerance $\tau>0$, such that every nonadaptive SQ learner that makes $t$ queries to $\mathcal O$, each with values in $\{+1,-1\}$ on labels $\{+1,-1\}$ and tolerance at least $2^{-d/3}$, satisfies: if the target $c_{\bar r,\bar a}$ is drawn uniformly from the $2^{d+1}$ MASKED-PARITY concepts, then the output hypothesis $h$ of the learner satisfies
--   $$\Pr_{c_{\bar r,\bar a}}\Bigl[\mathrm{err}(c_{\bar r,\bar a},h)\ge\tfrac14\Bigr]\ge\frac12-\frac t{2^{d/3+2}} .$$
--
--   MASKED-PARITY thus separates adaptive from nonadaptive statistical query learning under the uniform distribution, and, through the equivalence of SQ and local learning, interactive from noninteractive local learning.
--
--   **Formalization Note.** "Efficient" in part (1) is not modelled; the learner of part (1) is required to be exact on every valid answer, which is stronger than PAC learning with parameters $\alpha,\beta$. The informal clause "with a polynomial number of queries" of part (2) is the reading of the quantitative sentence beginning "Specifically", which is what is formalized. Part (2) exhibits the paper's oracle and asserts its validity, so the oracle cannot ignore the tolerance. The learner's hypothesis is any real-valued function on the domain, not necessarily a concept of the class. Learners are deterministic; for a randomized learner the bound holds for each fixing of its coins and hence on average. The probability over the target is the count of pairs $(\bar r,\bar a)$ divided by $2^{d+1}$; the pairs index the concepts injectively. $2^{d/3}$ is a real power. The index $i\in\{0,1\}^{\log d}$ is encoded as `Fin d`.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 27, Theorem 5.16

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle

namespace PrivLearn.MaskedParity

/-- **Theorem 5.16** (p. 27). Let `d` be a power of two and let the examples be uniform on the
domain `{0,1}^d × {0,1}^{log d} × {0,1}`.

1. There is an adaptive SQ learner for MASKED-PARITY with two rounds (`d` queries, then one), all
   queries `{0,1}`-valued and of tolerance at least `1/(4d+1)`, that outputs the target concept
   `c_{r,a}` for every target and every valid answers of the SQ oracle.
2. The oracle `𝒪` is a valid SQ oracle for every target (answers within `τ` of the true value for
   every query and every `τ > 0`), and every nonadaptive SQ learner making `t` queries, with values
   `±1` on labels `±1` and tolerances at least `2^{−d/3}`, run against `𝒪` on a target `c_{r̄,ā}`
   drawn uniformly from the `2^{d+1}` concepts, outputs a hypothesis `h` with
   `err(c_{r̄,ā}, h) ≥ 1/4` with probability at least `1/2 − t/2^{d/3+2}`. -/
theorem theorem_5_16 {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) :
    (∃ L : TwoRoundSQLearner (Dom d) d 1,
      (∀ j u y, L.q₁ j u y = 0 ∨ L.q₁ j u y = 1) ∧
      (∀ ans k u y, L.q₂ ans k u y = 0 ∨ L.q₂ ans k u y = 1) ∧
      (∀ j, 1 / (4 * (d : ℝ) + 1) ≤ L.τ₁ j) ∧
      (∀ ans k, 1 / (4 * (d : ℝ) + 1) ≤ L.τ₂ ans k) ∧
      ∀ (r : Fin d → ZMod 2) (a : ZMod 2) (ans₁ : Fin d → ℝ) (ans₂ : Fin 1 → ℝ),
        (∀ j, IsLabeledSQAnswer (cMP r a) (L.q₁ j) (L.τ₁ j) (ans₁ j)) →
        (∀ k, IsLabeledSQAnswer (cMP r a) (L.q₂ ans₁ k) (L.τ₂ ans₁ k) (ans₂ k)) →
        L.out ans₁ ans₂ = cMP r a) ∧
    (∀ (r : Fin d → ZMod 2) (a : ZMod 2) (g : Dom d → ℝ → ℝ) (τ : ℝ), 0 < τ →
      IsLabeledSQAnswer (cMP r a) g τ (oracleO r a g τ)) ∧
    (∀ (t : ℕ) (L : NonadaptiveSQLearner (Dom d) t),
      (∀ k, 1 / (2 : ℝ) ^ ((d : ℝ) / 3) ≤ L.τ k) →
      (∀ k u y, (y = 1 ∨ y = -1) → (L.q k u y = 1 ∨ L.q k u y = -1)) →
      1 / 2 - (t : ℝ) / (2 : ℝ) ^ ((d : ℝ) / 3 + 2) ≤
        ((Finset.univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
            1 / 4 ≤ errMP (cMP ra.1 ra.2)
              (L.out fun k => oracleO ra.1 ra.2 (L.q k) (L.τ k))).card : ℝ) /
          (2 : ℝ) ^ (d + 1)) := by sorry

end PrivLearn.MaskedParity
