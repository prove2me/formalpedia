-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_fidelity_bounds
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.fidelity_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:56:11.103026+00:00
-- url     : https://prove2.me/theorems/f945b0fd-4889-4ee9-b416-cb0bfb5052a4
-- title:
--   Eqs.(101)-(102) and following limit: fidelity bounds and convergence
-- statement:
--   For $N\ge1$ ports of local dimension $d\ge1$, let $\mathcal Y_N^{(d)}$ be the Young diagrams of $N$ boxes and height at most $d$. The physical teleportation matrix $M_N^{(d)}$ has diagonal equal to the number of removable corners and off-diagonal entry one exactly for distinct shapes related by a single-box move; all other entries vanish. Write $\lambda_{\max}$ for its largest eigenvalue and $F_{\mathrm{opt}}(N,d)$ for the maximum entanglement fidelity over the resource and Alice's measurement. Bob retains the named port and makes no unitary correction.
--
--   Let $F_{\mathrm{EPR}}(N,d)$ be the fixed-resource fidelity of the square-root measurement with $N$ maximally entangled pairs, given explicitly by Eq. (120). Then
--
--   $$\frac{N}{d^2+N-1}\le F_{\mathrm{EPR}}(N,d)\le F_{\mathrm{opt}}(N,d)\le1.$$
--
--   For every fixed $d\ge1$,
--
--   $$\lim_{N\to\infty}\frac{N}{d^2+N-1}=1,\qquad\lim_{N\to\infty}F_{\mathrm{opt}}(N,d)=1.$$
--
--   The rational quantity is only a lower bound for the EPR-resource fidelity. Fixing $d$ before the limit is essential.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 22, Eqs.(101)-(102) and following limit: fidelity bounds and convergence

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Eqs.(101)–(102) and the fixed-d squeeze limit (PDF p.22). The rational term
is a lower bound for the fixed EPR-resource fidelity, not its exact value. -/
theorem fidelity_bounds {d : ℕ} (hd : 0 < d) :
    (∀ N : ℕ, 0 < N →
      (N : ℝ) / ((d : ℝ)^2 + N - 1) ≤ eprFormula d (N-1) ∧
      eprFormula d (N-1) ≤ pbtOptimalFidelity d N ∧ pbtOptimalFidelity d N ≤ 1) ∧
    Tendsto (fun N : ℕ => (N : ℝ) / ((d : ℝ)^2 + N - 1)) atTop (nhds 1) ∧
    Tendsto (fun N : ℕ => pbtOptimalFidelity d N) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
