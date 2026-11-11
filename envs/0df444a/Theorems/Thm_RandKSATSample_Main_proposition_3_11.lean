-- Prove2me | Theorems.Thm_RandKSATSample_Main_proposition_3_11
-- name    : RandKSATSample.Main.proposition_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:59.072565+00:00
-- url     : https://prove2.me/theorems/69410092-bbaf-4cb2-ae3f-4969517643fa
-- title:
--   Proposition 3.11 — polymer-root estimate: given the structure and the bad signs, with probability ≥ 1 − ζ over the good signs, sup_a Σ_{γ∈CS_Ψ(a)} q_γ e^{(1+τ)|γ|} ≤ ρ
-- statement:
--   Let $k\ge30$, assume the joint event of Lemmas 3.1 to 3.3, $m\ge1$, and fix $\zeta\in(0,1)$ with $L=\lceil\log_2(32m/\zeta)\rceil\le r$. View $\Phi$ as generated in three stages: the structure (the variable of every occurrence, which fixes $V_{\mathrm{bad}}$, $V_{\mathrm{good}}$, $H_\Phi$, $G_\Phi$), the signs of the bad-variable occurrences, and the signs of the good-variable occurrences. Conditional on the first two, with probability at least $1-\zeta$ over the good-variable signs,
--   $$\sup_{a\in\mathcal C^{\mathrm{good}}}\sum_{\gamma\in\mathsf{CS}_\Psi(a)}q_\gamma e^{(1+\tau)|\gamma|}\le\rho\quad(3.6).$$
--   This is the polymer-root estimate that drives the cluster expansion of §4 and the residual sampler of §5.
--
--   **Formalization Note.** Conditioning on the structure and the bad signs of a given $\Phi$ is the uniform law on the formulas $\Phi'$ with the same variable at every occurrence and the same sign at every occurrence whose variable is bad; the probability is the fraction of these satisfying (3.6). The supremum over $\mathcal C^{\mathrm{good}}$ is written as "for every $a\in\mathcal C^{\mathrm{good}}$".
--
--   Differences from the source:
--   - reading: Assume the joint event of Lemmas 3.1 to 3.3 → hypotheses JointEvent Φ and k ≥ 30; reason: the joint event is that of Lemmas 3.1 and 3.3, which are stated for k ≥ 30, and the proof uses k ≥ 30 (p. 15, last display); without it the statement fails (k = 1, see INSIGHTS.yaml I1)
--   - encoding: sup_{a ∈ C_good} … ≤ ρ → ∀ a ∈ C_good, … ≤ ρ (PolyRoot); reason: a supremum over a finite set is at most ρ iff every term is; for empty C_good both hold
--   - encoding: conditional probability over the good-variable signs given the structure generation and the bad-variable signs → fraction of the formulas Φ' with the same occurrence variables as Φ and the same signs on bad-variable occurrences that satisfy PolyRoot; reason: the good-variable signs are independent fair bits given the first two stages, so the conditional law is uniform on these formulas
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 19, Proposition 3.11

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

open Classical

namespace RandKSATSample.Main

/-- Proposition 3.11: on the joint event of Lemmas 3.1–3.3 (whose lemmas assume `k ≥ 30`), with
`m ≥ 1`, `ζ ∈ (0,1)` and `L = ⌈log₂(32m/ζ)⌉ ≤ r`: conditional on the structure (the variables of
all occurrences) and on the signs of the bad-variable occurrences of `Φ`, with probability at
least `1 − ζ` over the signs of the good-variable occurrences, the polymer-root estimate (3.6)
`sup_{a ∈ C_good} Σ_{γ ∈ CS_Ψ(a)} q_γ e^{(1+τ)|γ|} ≤ ρ` holds. -/
theorem proposition_3_11 {n m k : ℕ} (hk : 30 ≤ k) (Φ : Formula n m k) (hJ : JointEvent Φ)
    (hm : 1 ≤ m) (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hL : ⌈Real.logb 2 (32 * m / ζ)⌉₊ ≤ rpar n m k) :
    let R : Finset (Formula n m k) := Finset.univ.filter fun Φ' =>
      ∀ (a : Fin m) (i : Fin k), (Φ' a i).1 = (Φ a i).1 ∧
        ((Φ a i).1 ∈ Vbad Φ → (Φ' a i).2 = (Φ a i).2)
    1 - ζ ≤ ((R.filter fun Φ' => PolyRoot Φ').card : ℝ) / (R.card : ℝ) := by sorry

end RandKSATSample.Main
