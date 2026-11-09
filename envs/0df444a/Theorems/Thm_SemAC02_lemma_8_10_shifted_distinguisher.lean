-- Prove2me | Theorems.Thm_SemAC02_lemma_8_10_shifted_distinguisher
-- name    : SemAC02.lemma_8_10_shifted_distinguisher
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:41.728233+00:00
-- url     : https://prove2.me/theorems/0df2c84b-0b52-4b9b-8ca8-372db1882bca
-- title:
--   Lemma 8.10 — a shifted coin distinguisher
-- statement:
--   Fix $d\ge2$. For all sufficiently small $\epsilon>0$ there exist an integer $m\ge1$ and a monotone, AND-rooted formula $T$ on $m$ input variables, of depth at most $d$ and size $\exp\bigl(O_d(\epsilon^{-1/(d-1)})\bigr)$, such that
--   $$
--   \Pr_{x\sim\mathrm{Bern}(1/2-\epsilon)^m}[T(x)=1]\le\tfrac15,\qquad \Pr_{x\sim\mathrm{Bern}(1/2)^m}[T(x)=0]\le\tfrac15 .
--   $$
--
--   The lemma moves the two biases of the coin problem to $1/2-\epsilon$ and $1/2$, which is what the covering gadget needs.
--
--   Differences from the source:
--   - encoding: O_d(ε^{−1/(d−1)}), "for all sufficiently small ε > 0" → one constant A (and ε₀ > 0) chosen before ε; ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); reason: standard reading of O_d(·) and "for all sufficiently small ε"; the constants depend on d only
--   - encoding: formula (circuit with the paper's conventions of p.17) and its size → Circ tree in normal form (IsReduced), size = treeSize (number of nodes); reason: the paper's circuits are flattened with no repeated children by definition; for a formula the size is its number of nodes
--   - encoding: Pr over Bern(p)^m → bernProb p, the explicit finite sum; reason: same numbers
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 8.10, p.66 (PDF p.68)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb

namespace SemAC02

/-- **Lemma 8.10 (A shifted coin distinguisher)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.10, p.66): fix
`d ≥ 2`. For all sufficiently small `ϵ > 0`, there exist an integer `m ≥ 1` and a monotone,
AND-rooted formula `T` on `m` input variables, of depth at most `d` and size
`exp(O_d(ϵ^{−1/(d−1)}))`, such that
`Pr_{x∼Bern(1/2−ϵ)^m}[T(x) = 1] ≤ 1/5` and `Pr_{x∼Bern(1/2)^m}[T(x) = 0] ≤ 1/5`.

**Formalization Note** `O_d(·)` is one constant `A` chosen before `ϵ`; "sufficiently small" is
`∃ ϵ₀ > 0, ∀ ϵ ∈ (0, ϵ₀)`. AND-rooted: the root is an AND gate. The formula is in the paper's
normal form (`IsReduced`); size is tree size. -/
theorem lemma_8_10_shifted_distinguisher (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧
        (∃ cs, T = Circ.and cs) ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        bernProb (1 / 2 - ε) (fun x => T.eval x) ≤ 1 / 5 ∧
        bernProb (1 / 2) (fun x => !T.eval x) ≤ 1 / 5 := by sorry

end SemAC02
