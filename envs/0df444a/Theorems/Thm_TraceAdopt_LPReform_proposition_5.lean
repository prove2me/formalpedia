-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_proposition_5
-- name    : TraceAdopt.LPReform.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:58.296442+00:00
-- url     : https://prove2.me/theorems/7f65245f-2e4d-428b-9f81-78c4b8c5b695
-- title:
--   Proposition 5, pp. 15–16 — binary program (4) solves MIN-SCTM
-- statement:
--   Let $s$ be a binary vector indexed by firms. It extends to a feasible solution $(s,\ell)$ of formulation (4) if and only if it is the indicator of a seed set $S$ that fully activates the SCTM network:
--
--   $$\exists\ell\ (s,\ell)\in\mathcal F_4\quad\Longleftrightarrow\quad \exists S\text{ fully activating},\ s=\mathbf1_S.$$
--
--   For every seeding-cost vector $w$, an optimal feasible solution of (4) yields $S^*_0=\{i:s^*_i=1\}$, a minimum-cost fully activating seed set, and its objective equals $\mathrm{OPT}(w)$. This is the correctness claim for the first binary reformulation.
--
--   **Formalization Note** The equivalence is the explicit feasibility correspondence stated in the proof on p. 38. The theorem includes the §3.1 standing assumptions. Costs are real-valued and may have either sign.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, pp. 15–16, Proposition 5, equations (4a)–(4d); p. 38, proof

import Definitions.Def_TraceAdopt_LPReform_BiLP4

namespace TraceAdopt.LPReform

/-- Proposition 5, pp. 15–16: (4) has exactly the feasible seed vectors of
MIN-SCTM, and an optimum of (4) gives a minimum-cost seed set. -/
theorem proposition_5 (I : Instance) (hI : I.Standing) :
    (∀ s : Fin I.n → ℕ,
      (∃ lFS lSF, BiLP4Feasible I s lFS lSF) ↔
        ∃ S : Finset (Fin I.n), FullyActivates I S ∧
          ∀ i, s i = if i ∈ S then 1 else 0) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (lFS : Fin I.n → Fin I.m → ℕ)
        (lSF : Fin I.m → Fin I.n → ℕ),
      BiLP4Feasible I s lFS lSF →
      (∀ (s' : Fin I.n → ℕ)
          (lFS' : Fin I.n → Fin I.m → ℕ)
          (lSF' : Fin I.m → Fin I.n → ℕ),
        BiLP4Feasible I s' lFS' lSF' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) := by sorry

end TraceAdopt.LPReform
