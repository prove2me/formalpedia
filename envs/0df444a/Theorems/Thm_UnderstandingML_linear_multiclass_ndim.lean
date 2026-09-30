-- Prove2me | Theorems.Thm_UnderstandingML_linear_multiclass_ndim
-- name    : UnderstandingML.linear_multiclass_ndim
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:58:13.533858+00:00
-- url     : https://prove2.me/theorems/675787e5-3cc5-41e5-9b4f-8b8db95f5ba0
-- title:
--   Theorem 29.7: the class H_Ψ = {x ↦ argmaxᵢ ⟨w, Ψ(x,i)⟩ : w ∈ ℝ^d} of linear multiclass predictors has Natarajan dimension ≤ d
-- statement:
--   **Theorem 29.7.** $\operatorname{Ndim}(H_\Psi) \le d$, for $H_\Psi = \{x \mapsto \operatorname{argmax}_{i \in [k]}\langle w, \Psi(x, i)\rangle : w \in \mathbb{R}^d\}$ (29.1).
--
--   Formally: ties in the argmax are broken towards the smallest label (some fixed rule is needed: with arbitrary tie-breaking every function is an argmax predictor of $\Psi \equiv 0$).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §29.3.3 pp. 405-406, Theorem 29.7 with its proof

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 29.7** (p. 406). For a class-sensitive feature mapping `Ψ : X × [k] → ℝ^d` and
`H_Ψ = {x ↦ argmaxᵢ ⟨w, Ψ(x, i)⟩ : w ∈ ℝ^d}` (29.1), `Ndim(H_Ψ) ≤ d`. Ties in the argmax are
broken towards the smallest label. -/
theorem linear_multiclass_ndim {X : Type*} {d k : ℕ} [NeZero k] (Ψ : X → Fin k → Vec d) :
    ndim (linearMulticlassClass Ψ) ≤ d := by sorry

end UnderstandingML
