-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_proposition_7
-- name    : TraceAdopt.LPReform.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:32.978706+00:00
-- url     : https://prove2.me/theorems/9f49fcb1-0329-4df8-8bef-99b9cc7b3b86
-- title:
--   Proposition 7, p. 16 — formulations (5) and (4) are equivalent
-- statement:
--   Let $(T',\{X'_z\})$ be a tree decomposition of the undirected auxiliary graph $G'$, and let $\mathcal F_4$ and $\mathcal F_5$ be the feasible regions of formulations (4) and (5) (the latter built on these bags). For every binary seed vector $s$,
--
--   $$\exists\ell:\ (s,\ell)\in\mathcal F_5\quad\Longleftrightarrow\quad\exists\ell:\ (s,\ell)\in\mathcal F_4 .$$
--
--   Moreover, for every real cost vector $w$, if $(s^*,\ell^*)$ minimizes $\sum_iw_is_i$ over $\mathcal F_5$, then $S_0^*=\{i\in N_F: s^*_i=1\}$ fully activates the network and $\sum_iw_is^*_i=\mathrm{OPT}(w)$: $S^*_0$ solves MIN-SCTM.
--
--   The two formulations have the same objective, so the equivalence of feasible seed vectors is the content of "Problems (5) and (4) are equivalent". Formulation (5) has $O((n+m)\omega'^3)$ constraints for a decomposition of width $\omega'$, against $O(n^2m^2)$ for (4).
--
--   **Formalization Note** The section assumes $T'$ binary (p. 16); neither formulation (5) nor the proof on pp. 38–39 uses it, and the statement is made for every tree decomposition of $G'$. The feasibility correspondence is the one the proof establishes. The §3.1 standing assumptions are hypotheses.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 16, Proposition 7; pp. 38–39, proof

import Definitions.Def_TraceAdopt_LPReform_BiLP4
import Definitions.Def_TraceAdopt_LPReform_BiLP5

namespace TraceAdopt.LPReform

/-- Proposition 7, p. 16: for a tree decomposition of `G′`, formulations (5) and (4)
have the same feasible seed vectors, and an optimal solution of (5) gives a
minimum-cost fully activating seed set. -/
theorem proposition_7 (I : Instance) (hI : I.Standing) {T : Type} [Fintype T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (hX : RobertsonSeymour1986.GM5.IsTreeDecomposition (auxGraph I) t X') :
    (∀ s : Fin I.n → ℕ,
      (∃ ℓ, BiLP5Feasible I X' s ℓ) ↔ ∃ lFS lSF, BiLP4Feasible I s lFS lSF) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ),
      BiLP5Feasible I X' s ℓ →
      (∀ (s' : Fin I.n → ℕ) (ℓ' : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ),
        BiLP5Feasible I X' s' ℓ' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) := by sorry

end TraceAdopt.LPReform
