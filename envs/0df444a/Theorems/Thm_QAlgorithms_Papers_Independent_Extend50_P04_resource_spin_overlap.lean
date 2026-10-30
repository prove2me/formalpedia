-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_resource_spin_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.resource_spin_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:14:23.269487+00:00
-- url     : https://prove2.me/theorems/274e601f-916b-4b51-a2e8-77e8b2488f45
-- title:
--   Appendix G unnumbered result: angular-momentum resource fidelity
-- statement:
--   Let $N\ge1$ and use the normalized explicit qubit principal coefficients (87)/(E5) to construct $O_N$ by (84). Let $R_{N,2}=|\langle\Phi^+|(O_N\otimes I)|\Phi^+\rangle|$. With twice-spin index $t=2j$, one has
--   $$R_{N,2}=\sqrt{\frac{N!}{2^{N-2}(N+2)}}\sum_{\substack{0\le t\le N\\t\equiv N\pmod2}}\frac{(t+1)\sin(\pi(t+1)/(N+2))}{\sqrt{((N-t)/2)!\,((N+t)/2+1)!}}.$$
--   Parity makes both factorial arguments integers. This evaluates the resource overlap in angular-momentum coordinates.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 26, Appendix G unnumbered result: angular-momentum resource fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.26, Appendix G, (G6): angular-momentum expression for the actual qubit resource overlap.
Twice-spin parity indexing and real exponent N-2 include N=1 faithfully. -/
theorem resource_spin_overlap (N : ℕ) (hN : 1 ≤ N) :
    resourceFidelity 2 N (resourceOperation 2 N (qubitCoefficients N)) = spinFormula N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
