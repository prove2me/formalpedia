-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_lb_metric
-- name    : RankCutFacility.Shifted.Supplement.lb_metric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:21:59.284832+00:00
-- url     : https://prove2.me/theorems/0c1b7bab-3761-489d-88ec-0bd7f535b4c6
-- title:
--   Lemma 6.2 — The distance of Section 6.1 is a metric
-- statement:
--   Fix $N\ge2$, $m=2N(N-1)$, demand locations $X=\{x_1,\dots,x_m\}$ and facilities $Y=\{y_I:I\subseteq[m],|I|=N\}$. Define $d$ on $X\cup Y$ by $d(z,z)=0$, $d(x_i,x_j)=2/3$ for $i\ne j$, $d(y_I,y_{I'})=2/3$ for $I\ne I'$, and symmetrically
--
--   $$d(x_i,y_I)=\begin{cases}1/3,& i\in I,\\ 1,& i\notin I.\end{cases}$$
--
--   **Lemma 6.2.** $d$ is a metric on $X\cup Y$: $d(a,b)=0$ iff $a=b$, $d(a,b)=d(b,a)$, and $d(a,c)\le d(a,b)+d(b,c)$ for all points.
--
--   This makes the instance of Theorem 6.1 and Corollary 6.7 a genuine metric facility-location instance.
--
--   Differences from the source:
--   - encoding: d is a metric on X ∪ Y → lbDist on Fin m ⊕ {I : Finset (Fin m) // I.card = N} satisfies identity of indiscernibles, symmetry and the triangle inequality; reason: nonnegativity follows from these three axioms, so this is the definition of a metric
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Lemma 6.2, printed p. 19 (PDF p. 21)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

noncomputable section

namespace RankCutFacility.Shifted.Supplement

/-- Lemma 6.2 (PDF p. 21, printed p. 19): the distance of Section 6.1 is a metric on `X ∪ Y`. -/
theorem lb_metric (N : ℕ) (hN : 2 ≤ N) :
    (∀ a b : LBPoint N, lbDist N a b = 0 ↔ a = b) ∧
    (∀ a b : LBPoint N, lbDist N a b = lbDist N b a) ∧
    (∀ a b c : LBPoint N, lbDist N a c ≤ lbDist N a b + lbDist N b c) := by sorry

end RankCutFacility.Shifted.Supplement
