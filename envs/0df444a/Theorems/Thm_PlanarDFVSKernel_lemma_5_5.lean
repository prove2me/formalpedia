-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_5_5
-- name    : PlanarDFVSKernel.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:30.306043+00:00
-- url     : https://prove2.me/theorems/bbaebb64-4d5f-47b0-a3b6-e0779c3f565e
-- title:
--   Lemma 5.5 — Reduction Rule 7 preserves solvability
-- statement:
--   **Lemma 5.5.** Reduction Rule 7 preserves whether at most $k$ groups in total can make every weakly connected component strongly connected.
--
--   For every compression setting — a GSCA instance with acyclic base graph, single-arc ordinary groups, every available reverse arc closing a base path and every base arc covered by an available reverse arc (the properties of Lemmas 4.3–4.4) — the instance is a YES-instance if and only if the instance produced by Reduction Rule 7 (merging, within each weakly connected component, the vertices outside $W$ with equal distance records, followed by normalization) is a YES-instance.
--
--   Differences from the source:
--   - generalization: the dual instance I₂ after Rule 6 (§5.1) → any CompressionSetting, without planarity or dual; reason: these are the properties the proof uses (via Lemmas 5.3, 5.4); the paper's instance satisfies them
--   - encoding: identification classes within each component by the record over W_C → class key (weak component, full record over W); reason: a retained vertex outside the component has d_L = ∞, so the full record adds only the constant k + 1
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.5, p.25 (PDF 26)

import Mathlib
import Definitions.Def_PlanarDFVSKernel_GSCA
import Definitions.Def_PlanarDFVSKernel_CompressionSetting
import Definitions.Def_PlanarDFVSKernel_CompressionSetting_rule7

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **Lemma 5.5** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.5, p.25 (PDF 26)): "Reduction Rule 7 preserves whether at most k
groups in total can make every weakly connected component strongly connected."

For every `CompressionSetting` (the properties of Lemmas 4.3–4.4, on all weakly connected components
at once), the GSCA instance is a YES-instance exactly when the instance produced by Reduction Rule 7
(quotient by the identification classes within each weakly connected component, then normalization
(i)–(iii), same `k`) is a YES-instance.

**Formalization Note** No planarity is assumed. The GSCA group condition ("absent from H, with all
endpoints in the same weakly connected component") is not a separate hypothesis: it follows from the
setting (an available arc `t → s` closes a base path `s ⇝ t`, so it lies in one component, and it is
not a base arc since `H` is acyclic). -/
theorem lemma_5_5 {V : Type*} [Fintype V] [DecidableEq V] (C : CompressionSetting V) :
    C.I.Solvable ↔ C.rule7.Solvable := by sorry

end PlanarDFVSKernel
