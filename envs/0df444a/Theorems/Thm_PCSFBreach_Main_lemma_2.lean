-- Prove2me | Theorems.Thm_PCSFBreach_Main_lemma_2
-- name    : PCSFBreach.Main.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:07.494201+00:00
-- url     : https://prove2.me/theorems/23e2bef7-acc2-4307-9dff-84caa7c96ee3
-- title:
--   Lemma 2 — a minimal subforest of the grown forest connecting D′ costs at most 2·y(H)
-- statement:
--   Let $\lambda>0$, $\mu\ge 0$, let $I$ be a PCSF instance and consider any run of the parametric primal-dual algorithm on $I$, with final grown forest $F'$, moats $H$ with final duals $y_U$, and $D'=D\setminus Q$. If $\hat F\subseteq F'$ connects every pair of $D'$ and no proper subset of $\hat F$ does (an inclusion-wise minimal subforest of $F'$ connecting $D'$), then
--   $$c(\hat F)\le 2\cdot y(H)=2\sum_{U\in H}y_U .$$
--
--   This is the standard primal-dual cost bound; with $\pi(Q)$ added it gives the cost of the first candidate of Algorithm 1 (Lemma 3).
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 7, Lemma 2 (proof in Appendix B, p. 48)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_PrimalDual
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Lemma 2 (p. 7): an inclusion-wise minimal subforest of the final grown forest connecting `D′`
has edge cost at most `2 · y(H)`. -/
theorem lemma_2 (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 ≤ μ) (I : Instance) (R : PDRun I)
    (hR : IsPDRun I lam μ R) (Fhat : Finset I.Edge)
    (hmin : I.IsMinimalConnecting Fhat (R.D' lam) R.finalForest) :
    I.edgeCost Fhat ≤ 2 * R.yH := by sorry

end PCSFBreach.Main
