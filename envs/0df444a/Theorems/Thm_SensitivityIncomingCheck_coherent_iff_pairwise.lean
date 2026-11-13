-- Prove2me | Theorems.Thm_SensitivityIncomingCheck_coherent_iff_pairwise
-- name    : SensitivityIncomingCheck.coherent_iff_pairwise
-- status  : Proved
-- author  : @jennyuxi
-- created : 2026-11-12T23:38:06.662936+00:00
-- url     : https://prove2.me/theorems/d883cd8b-14aa-4296-bc0b-f3f353566b10
-- title:
--   Coherent colorings can be checked without enumerating colors
-- statement:
--   Let $V$ be any vertex type, let $L$ be a finite list of vertices, let $A(i,j)$ specify directed edges, and let $\ell(i,j)\in\{0,1\}$ label those edges. Repeated vertices in $L$ are allowed. Then
--
--   $$
--   \exists c:V\to\{0,1\},\quad
--   \forall i,j\in L,\ A(i,j)\Rightarrow\ell(i,j)=c(j)
--   \quad\Longleftrightarrow\quad
--   \forall j,i,k\in L,\ A(i,j)\land A(k,j)\Rightarrow\ell(i,j)=\ell(k,j).
--   $$
--
--   The right side is implemented by three finite list scans. For a list of length $m$, it requires at most $m^3$ label comparisons and does not enumerate colorings of the entire vertex type. The statement also covers an empty list and vertices with no incoming edges. No tournament, regularity, looplessness, or finiteness assumption on $V$ is needed.
--
--   This eliminates the color quantifier in the ordinary coherence clause and the corresponding source-set coherence test used by the sensitivity graph certificate search. It does not remove subset enumeration or address positive defect budgets.
-- source:
--   Original supporting lemma derived from the coherence condition in SensitivityGraphLocal.LocalValid, https://prove2.me/definitions/dcea1f09-465d-415f-bd27-bf34eb61c716, ordinary-cutoff clause (eighth conjunct) and zero-defect source clause (tenth conjunct); underlying RawData.Valid at https://prove2.me/definitions/e1bc7543-e6c9-4767-be0c-1d4085276993. The color-elimination equivalence and executable list scan are proved here, rather than attributed to a theorem in the source.

import Lean
set_option autoImplicit false

theorem SensitivityIncomingCheck.coherent_iff_pairwise {V : Type} (vertices : List V)
    (adj : V → V → Bool) (label : V → V → Fin 2) :
    (vertices.all fun j => vertices.all fun i => vertices.all fun k =>
      decide (adj i j = true → adj k j = true → label i j = label k j)) = true ↔
    ∃ colors : V → Fin 2,
      ∀ i, i ∈ vertices → ∀ j, j ∈ vertices →
        adj i j = true → label i j = colors j := by sorry
