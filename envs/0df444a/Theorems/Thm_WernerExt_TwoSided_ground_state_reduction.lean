-- Prove2me | Theorems.Thm_WernerExt_TwoSided_ground_state_reduction
-- name    : WernerExt.TwoSided.ground_state_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:35.655486+00:00
-- url     : https://prove2.me/theorems/533d4470-6404-4308-a39c-eb2ca4a25ec2
-- title:
--   p. 2, Extendibility as a ground state problem — ρ_W(α) is (n_A, n_B)-extendible iff α ≥ min Spect(H_W)
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$ and $\alpha\in[-1,1]$. Then the Werner state $\rho^W(\alpha)$ is $(n_A,n_B)$-extendible if and only if
--   $$\alpha\ \ge\ \min\operatorname{Spect}(H^W).$$
--   Equivalently, the extendible Werner states form the parameter interval $[\alpha_{n_A,n_B},1]$ with $\alpha_{n_A,n_B}=\min\operatorname{Spect}(H^W)$.
--
--   This reduces the extendibility problem to the ground state problem of $H^W$.
--
--   **Formalization Note** “$\alpha\ge\min\operatorname{Spect}(H^W)$” is written as: some real eigenvalue $e$ of $H^W$ satisfies $e\le\alpha$; the two agree because the spectrum is finite and nonempty.
--
--   Differences from the source:
--   - encoding: α ≥ min Spect(H_W), with α_{n_A,n_B} the smallest extendible parameter → ∃ e, e is an eigenvalue of H_W and e ≤ α; reason: equivalent for a finite nonempty spectrum; avoids an infimum
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 2, *Extendibility as a ground state problem*, 'Consequently, the smallest eigenvalue of H^W must be equal to α_{nA,nB} …'; p. 2, 'they correspond to a parameter interval [α_{nA,nB}, 1]'

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

/-- p. 2, *Extendibility as a ground state problem*: the smallest eigenvalue of `H_W` is
`α_{nA,nB}`, i.e. `ρ_W(α)` is `(nA, nB)`-extendible iff `α ≥ min Spect(H_W)`. -/
theorem ground_state_reduction (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB)
    (α : ℝ) (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    IsExtendible d nA nB (wernerState d α) ↔
      ∃ e : ℝ, IsEigenvalue (hamW d nA nB) e ∧ e ≤ α := by sorry

end WernerExt.TwoSided
