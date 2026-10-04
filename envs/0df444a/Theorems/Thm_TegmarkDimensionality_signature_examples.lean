-- Prove2me | Theorems.Thm_TegmarkDimensionality_signature_examples
-- name    : TegmarkDimensionality.signature_examples
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T05:23:34.934984+00:00
-- url     : https://prove2.me/theorems/9089b6bc-4c4a-42d7-a41f-c248926f0659
-- title:
--   Signatures $(+---)$, $(+++++)$, $(++--)$: hyperbolic, elliptic, ultrahyperbolic
-- statement:
--   The field equations with coefficient matrix $A=g^{-1}$ are
--
--   1. **hyperbolic** for the metric $g=\operatorname{diag}(1,-1,-1,-1)$ of signature $(+---)$, i.e. $(n,m)=(3,1)$;
--   2. **elliptic** for $g=\operatorname{diag}(1,1,1,1,1)$ of signature $(+++++)$;
--   3. **ultrahyperbolic** for $g=\operatorname{diag}(1,1,-1,-1)$ of signature $(++--)$.
--
--   These are the three examples the paper gives for the classification.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L73, second paragraph ('hyperbolic in a metric of the signature (+---), ... elliptic in a metric of the signature (+++++), and ultrahyperbolic in a metric of the signature (++--)')

import Mathlib
import Definitions.Def_tegmark_pde_classification

namespace TegmarkDimensionality

/-- The field equations are hyperbolic for the metric of signature `(+ - - -)`, elliptic
for `(+ + + + +)` and ultrahyperbolic for `(+ + - -)`. -/
theorem signature_examples :
    IsHyperbolic (Matrix.diagonal (![1, -1, -1, -1] : Fin 4 → ℝ))⁻¹ ∧
      IsElliptic (Matrix.diagonal (![1, 1, 1, 1, 1] : Fin 5 → ℝ))⁻¹ ∧
      IsUltrahyperbolic (Matrix.diagonal (![1, 1, -1, -1] : Fin 4 → ℝ))⁻¹ := by sorry

end TegmarkDimensionality
