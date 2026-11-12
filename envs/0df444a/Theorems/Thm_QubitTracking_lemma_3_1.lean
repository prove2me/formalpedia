-- Prove2me | Theorems.Thm_QubitTracking_lemma_3_1
-- name    : QubitTracking.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:34:16.779112+00:00
-- url     : https://prove2.me/theorems/e843185e-cbf4-48c9-8df4-fb8606822850
-- title:
--   Lemma 3.1 ([Unr14]) — reprogramming the random oracle at $x_l\oplus x_r$ inside the joint future light cone is undetectable
-- statement:
--   Let $\mathcal O_{\mathsf{random}}$ be a random oracle with exponential domain and image size, both powers of $2$. No QPT prover can distinguish, with noticeable probability, between:
--
--   1. $\mathcal V_L$ broadcasting a uniform $x_l$ at time $t_l$ and $\mathcal V_R$ a uniform $x_r$ at time $t_r$; and
--   2. the same, with $\mathcal O_{\mathsf{random}}$ reprogrammed to a uniform output $y$ on input $x_l\oplus x_r$ at every spacetime point $(p,t)$ with $t-t_l\ge p+1$ and $t-t_r\ge1-p$.
--
--   This lets the reductions of §8–§9 plant the game's challenge oracles at the claimed spacetime points.
--
--   Differences from the source:
--   - reading: a random oracle with exponential domain and image size, a power of 2 → a uniformly random 𝒪_random : 𝔽₂^λ → 𝔽₂^{m(λ)} with m polynomially bounded and m(λ) ≥ λ; reason: domain and image of size 2^λ and 2^m
--   - reading: any QPT prover → any QPT family of spacetime provers (Prover, IsQPT) with no input, the challenges in their message cells, one oracle; t_l, t_r arbitrary functions of λ; reason: the paper's §3.2 model, pinned down
--   - reading: cannot distinguish with noticeable probability → a negligible ν(λ) bounds, for every two-outcome measurement, the difference of its acceptance probabilities on the final states of all the prover's cells (averaged over all randomness) in the two cases; reason: a bound on the trace distance of the whole final state bounds every distinguisher
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 3.1, p.23

import Definitions.Def_QubitTracking_rhoReprog31

set_option autoImplicit false

namespace QubitTracking

/-- **Lemma 3.1** ([Unr14]; Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and
Time*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 3.1, p.23). Let `𝒪_random` be a
random oracle with exponential domain and image size, both powers of `2`. No QPT prover can
distinguish with noticeable probability between
* `𝒱_L` broadcasting a uniform `x_l` at time `t_l` and `𝒱_R` a uniform `x_r` at time `t_r`, and
* the same, with `𝒪_random` reprogrammed to a uniform output `y` on input `x_l ⊕ x_r` at every
  spacetime point `(p, t)` with `t − t_l ≥ p + 1` and `t − t_r ≥ 1 − p`.

Pinned down: `𝒪_random : 𝔽₂^λ → 𝔽₂^{m(λ)}` uniform with `m` polynomially bounded and `m(λ) ≥ λ`;
`t_l, t_r` arbitrary functions of `λ`; the prover any QPT family in the spacetime model; the
conclusion is a negligible bound, uniform over all two-outcome measurements, on the advantage of
distinguishing the final states of all the prover's cells (averaged over all randomness). -/
theorem lemma_3_1 (m : ℕ → ℕ) (hm : PPADSIS.SubexpSIS.PolyBounded m) (hml : ∀ l, l ≤ m l)
    (tl tr : ℕ → ℝ) (P : (l : ℕ) → Prover31 l (m l) (tl l) (tr l)) (hP : IsQPT P) :
    ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
      ∀ l, TDLe (rhoReal31 (P l)) (rhoReprog31 (P l)) (ν l) := by sorry

end QubitTracking
