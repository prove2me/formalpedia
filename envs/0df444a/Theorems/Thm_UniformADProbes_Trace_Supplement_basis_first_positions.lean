-- Prove2me | Theorems.Thm_UniformADProbes_Trace_Supplement_basis_first_positions
-- name    : UniformADProbes.Trace.Supplement.basis_first_positions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:20:19.523646+00:00
-- url     : https://prove2.me/theorems/feb42710-ca48-4fc0-95e4-041f0642d6fb
-- title:
--   Lemma A.1 — A basis in the first positions
-- statement:
--   Let $N\ge2$, and let $T$ be any finite connected simple tree of order $n\le N$. Write $\mathcal M_T$ for the real principal module spanned by all word responses from $\mathbf1$, including the empty word. Put $r=\dim_{\mathbb R}\mathcal M_T$, and use the exact polynomials $Z_i$ of equation (13), with $H_0=(M-1)R\,2^{(N-2)(M-2)}$ and $\tau=N!H_0^{N-1}+2$. Then
--   $$
--   (z_0,z_1,\ldots,z_{r-1})\text{ is linearly independent},\qquad
--   z_i\in\mathcal M_T\quad(0\le i<N),\qquad z_i=Z_i(A_T,D_T)\mathbf1.
--   $$
--   This fixed prefix is a basis of the principal module and supports the companion cyclic-matrix construction. The case $r=1$, including a singleton tree, is retained.
--
--   **Formalization Note** All spans and independence are over the reals after casting the integer adjacency and degree matrices. The rendered PDF's $H_0$ formula is used; no sufficiently-large-integer parameter replaces its specified specialization.
--
--   Differences from the source:
--   - encoding: finite connected trees and the first r responses → simple trees on Fin n, r given by real finrank, with the prefix indexed by Fin r; reason: labelling covers all finite trees and IsTree includes nonemptiness; the prefix has exactly r members
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Lemma A.1, p. 11 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_Supplement_rank_condensation

set_option autoImplicit false

namespace UniformADProbes.Trace.Supplement

theorem basis_first_positions (N : ℕ) (hN : 2 ≤ N) (n : ℕ) (hn : n ≤ N)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ (treeModule T)) =>
      condensedResponse N T i.val) ∧
    (∀ i : Fin N, condensedResponse N T i.val ∈ treeModule T) := by sorry

end UniformADProbes.Trace.Supplement
