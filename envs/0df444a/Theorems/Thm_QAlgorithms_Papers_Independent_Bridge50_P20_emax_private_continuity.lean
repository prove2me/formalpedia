-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P20_emax_private_continuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P20.emax_private_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:58:10.411492+00:00
-- url     : https://prove2.me/theorems/aacb59d3-309a-4ef2-bc7d-95883aba887e
-- title:
--   Full trace-norm continuity of max-relative entanglement
-- statement:
--   Let $d,s,t$ be positive integers. Alice and Bob have key registers of dimension $d$ and shield registers of dimensions $s$ and $t$, respectively. Let $\rho$ be a normalized density operator on the full key-and-shield system, and let $\gamma_d$ be any private state with key dimension $d$, constructed by a controlled twisting unitary from a maximally entangled key and an arbitrary normalized joint shield state. If $0\le\epsilon<2$ and the full trace norm satisfies $\|\rho-\gamma_d\|_1=\epsilon$, then
--
--   $$
--   E_{\max}(\rho)\ge \log_2 d+2\log_2(1-\epsilon/2).
--   $$
--
--   There is no bound on either shield dimension in terms of $d$. One-dimensional shields include maximally entangled targets. This is property P1 with $g=1$ and $f(\epsilon)=-2\log_2(1-\epsilon/2)$; the error is not half the trace norm.
-- source:
--   Versatile relative entropy bounds for quantum networks, arXiv:1707.05543v2, PDF p. 11, §III A, (25)–(26): P1 for E_max

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P20

open QAlgorithms QAlgorithms.Entanglement

-- Reuse pinned accepted definitions; source-specific conventions are audited below.

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P53 (amplitudeDamping)

open QAlgorithms.Papers.Independent.Information100.P75 (mixedIdentity)

open QAlgorithms.Papers.Independent.Next46.P29 (zRotation)

open QAlgorithms.Papers.Independent.Support50.P11 (choiState)

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1707.05543v2, PDF p.11, (25)-(26): P1 for Emax with full trace-norm
error epsilon, including both shields. All finite shield dimensions are allowed;
one-dimensional shields include maximally entangled targets. -/
theorem emax_private_continuity
    (d s t : ℕ) (hd : 0 < d) (hs : 0 < s) (ht : 0 < t)
    (rho phi : Matrix ((Fin d × Fin s) × (Fin d × Fin t))
      ((Fin d × Fin s) × (Fin d × Fin t)) ℂ)
    (hrho : IsDensityMatrix rho) (hphi : IsPrivateTarget phi)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he2 : epsilon < 2)
    (herr : traceNorm (rho - phi) = epsilon) :
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    letI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
    ((Real.logb 2 d + 2 * Real.logb 2 (1 - epsilon / 2) : ℝ) : EReal) ≤
      stateEMax rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P20

end
