-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_exact_distillation_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.exact_distillation_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:53:56.724775+00:00
-- url     : https://prove2.me/theorems/bdfb6116-da96-4944-997c-91704f3771ec
-- title:
--   Unnumbered Eqs.(87)–(88): conditional exact singlet bound
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $n\ge1$, $0\le m\le n$, and let $\sigma$ be a density matrix. Assume $E_R(\sigma^{\otimes n})=nE_R(\sigma)$ across the grouped cut. Suppose a complete product-Kraus channel sends the entire input $\sigma^{\otimes n}$ exactly to $|\Phi_m\rangle\langle\Phi_m|\otimes\omega$, where $\omega$ is a separable normalized residual state. Then
--
--   $$m\ln2\le nE_R(\sigma).$$
--
--   The channel may depend on $\sigma$. This is the conditional exact fixed-output idealization, with no dropped success probability or approximate asymptotic capacity claim.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 30, Unnumbered Eqs.(87)–(88): conditional exact singlet bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.30–32, Eqs.(87)–(88): conditional exact fixed-output singlet bound.
Additivity for the input copies is assumed, and the COMPLETE map produces the exact
Bell target with separable residual output. In nats the bound is m ln 2, not m. -/
theorem exact_distillation_bound {I J A B K : Type}
    [Fintype I] [Fintype J] [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
    [Nonempty I] [Nonempty J] [Nonempty A] [Nonempty B]
    (sigma : Matrix (I × J) (I × J) ℂ) (hsigma : IsDensityMatrix sigma)
    (n m : ℕ) (hn : 1 ≤ n) (hm : m ≤ n)
    (hadd : relativeEntanglementNats (copies sigma n) = (n : EReal) * relativeEntanglementNats sigma)
    (residual : Matrix (A × B) (A × B) ℂ) (hresidual : IsSeparableDensity residual)
    (L : K → Matrix (Qubits m × A) (Fin n → I) ℂ)
    (R : K → Matrix (Qubits m × B) (Fin n → J) ℂ)
    (hcomplete : ProductComplete L R)
    (hout : krausApply (fun k => Matrix.kronecker (L k) (R k)) (copies sigma n) =
      groupedProduct (pureDensity (maxEntangled m)) residual) :
    ((m : ℝ) * Real.log 2 : EReal) ≤ (n : EReal) * relativeEntanglementNats sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
