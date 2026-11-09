-- Prove2me | Theorems.Thm_TermCycDich_isRedMinor_trans
-- name    : TermCycDich.isRedMinor_trans
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:43:50.947206+00:00
-- url     : https://prove2.me/theorems/63af8a5d-76f8-4b2a-8571-e83b540148b7
-- title:
--   Proof of Theorem 1.1 — red-minors are transitive
-- statement:
--   If $(H,B)$ is a red-minor of $(G,R)$ and $(G,R)$ is a red-minor of $(K,T)$, then $(H,B)$ is a red-minor of $(K,T)$.
--
--   The proof of Theorem 1.1 uses it to pass from "$(H,R')$ contains $(\Gamma_{c^*}, V(\Gamma_{c^*}))$" and "$(\Gamma_{c^*}, V(\Gamma_{c^*}))$ contains $(G^*,R)$" to "$(H,R')$ contains $(G^*,R)$".
--
--   Differences from the source:
--   - generalization: annotated graphs (finite graphs) → graphs on arbitrary vertex types; reason: the finite case is a special case
--   - encoding: minor models with edge paths → branch-set minor models; reason: the two models give the same red-minor relation (p.15)
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), proof of Theorem 1.1, p.67 (PDF 69)

import Mathlib
import Definitions.Def_TermCycDich_IsRedMinor

namespace TermCycDich

/-- **Red-minors are transitive**: a red-minor of a red-minor of `(K, T)` is a red-minor of
`(K, T)`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), proof of Theorem 1.1, p.67 (PDF 69): "If any graph in C has bidimensionality at least c*,
then it contains an annotated graph (H, R′), which contains (Γ_{c*}, V(Γ_{c*})) as a red-minor by
definition. Note that (H, R′) also contains (G*, R) as a red-minor".

**Formalization Note** Stated for arbitrary vertex types (finite or not). -/
theorem isRedMinor_trans {U W V : Type} {H : SimpleGraph U} {B : Set U} {G : SimpleGraph W}
    {R : Set W} {K : SimpleGraph V} {T : Set V} (h₁ : IsRedMinor H B G R)
    (h₂ : IsRedMinor G R K T) : IsRedMinor H B K T := by sorry

end TermCycDich
