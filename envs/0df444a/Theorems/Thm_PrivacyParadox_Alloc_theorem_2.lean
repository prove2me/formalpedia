-- Prove2me | Theorems.Thm_PrivacyParadox_Alloc_theorem_2
-- name    : PrivacyParadox.Alloc.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:36.260976+00:00
-- url     : https://prove2.me/theorems/51e2d324-2f05-4124-9269-6d558b241de0
-- title:
--   Theorem 2, p. 13 (discrete form, App. C (55), p. 27) — a minimax-optimal allocation is constant χ for φ_k ≤ φ̂ and η/√φ_k above
-- statement:
--   Consider the discrete min-max program (39) after sorting: cells $k=1,\dots,K$ with weights $\pi_k>0$, $\sum_k\pi_k=\bar\theta^*\in(0,1]$, strictly increasing virtual costs $0<\phi_1<\dots<\phi_K$, $\gamma\in(0,1]$, $s\ge1$ agents, and budget data with $B/s-l>0$ (40). The analyst minimizes the worst case $\max_p U(A,p)$ over feasible allocations ($0<A_k\le1$, $\sum_k\pi_k\phi_kA_k+l\le B/s$), the adversary choosing $0\le p_k\le1$.
--
--   Then there are constants $\chi$, $\eta$, $\hat\phi$ and a feasible, non-increasing allocation $A^*$ of the form
--   $$A^*_k=\begin{cases}\chi,&\phi_k\le\hat\phi,\\[2pt] \dfrac{\eta}{\sqrt{\phi_k}},&\hat\phi<\phi_k,\end{cases}$$
--   which is minimax optimal: for every feasible $A$ and every admissible $p$ there is an admissible $p'$ with $U(A^*,p)\le U(A,p')$, i.e. $\max_pU(A^*,p)\le\max_pU(A,p)$.
--
--   This is the paper's main result on the bias–variance trade-off: the optimal selection probability is flat on low virtual costs and inversely proportional to the square root of the virtual cost above a threshold.
--
--   **Formalization Note** The paper states Theorem 2 for continuous costs and proves it in Appendix C for discrete costs, passing to the continuum by a limit $K\to\infty$ that is asserted, not proved; this is the discrete statement (55). The constants are existential, as the printed theorem leaves them to (78). Assumptions 1–4 enter through the positivity and sorting of the virtual costs and the shape of the program, not as separate hypotheses. The page's assumption (41) is not needed: when it fails, $A\equiv1$ is optimal and of the stated form. Allocations are required to be positive (Lean's $p/0=0$); strictly increasing $\phi_k$ is the sorted list of p. 25. The comparison is with every feasible allocation, so the statement is not the best-response property of Lemma 3.
-- source:
--   Liao, Su, Ziani, Wierman, Huang, arXiv:2105.14262v1, p. 13, Theorem 2, (21); App. C pp. 23–36, (39), (55)

import Mathlib
import Definitions.Def_PrivacyParadox_Alloc_Model

namespace PrivacyParadox.Alloc

theorem theorem_2 (P : Prog) (hP : P.Standing) :
    ∃ Astar : ℕ → ℝ, ∃ χ η φhat : ℝ,
      (∀ k ∈ Finset.Icc 1 P.K,
          (P.phi k ≤ φhat → Astar k = χ) ∧ (φhat < P.phi k → Astar k = η / Real.sqrt (P.phi k))) ∧
      P.FeasA Astar ∧ AntitoneOn Astar (Set.Icc 1 P.K) ∧
      ∀ A : ℕ → ℝ, P.FeasA A → ∀ p : ℕ → ℝ, P.AdmP p →
        ∃ p' : ℕ → ℝ, P.AdmP p' ∧ P.U Astar p ≤ P.U A p' := by sorry

end PrivacyParadox.Alloc
