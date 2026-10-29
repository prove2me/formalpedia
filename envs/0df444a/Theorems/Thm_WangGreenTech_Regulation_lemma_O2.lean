-- Prove2me | Theorems.Thm_WangGreenTech_Regulation_lemma_O2
-- name    : WangGreenTech.Regulation.lemma_O2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:34:45.616196+00:00
-- url     : https://prove2.me/theorems/114b49c1-dcd0-4534-9b0e-46906f4573a9
-- title:
--   Lemma O2 — monotonicity of the adoption-existence bound
-- statement:
--   Fix $0\le q<1$ and $r>0$. For $C\ge0$, define
--   $$B(\epsilon,C,r)=\inf\left(\left\{\frac{2\epsilon+Ct^r}{t}:0<t\le1\right\}\cup\left\{\frac{2\epsilon+C(1-s^r)}{1-s}:0\le s<1\right\}\right).$$
--
--   For each fixed payoff difference $d=f_H-m_L>0$, the map $\epsilon\mapsto B(\epsilon,(1-q)d,r)$ is strictly increasing on $\epsilon>0$. For each fixed $\epsilon>0$, the map $d\mapsto B(\epsilon,(1-q)d,r)$ is strictly increasing on $d>0$:
--   $$\epsilon_1<\epsilon_2\implies B(\epsilon_1,(1-q)d,r)<B(\epsilon_2,(1-q)d,r),$$
--   $$d_1<d_2\implies B(\epsilon,(1-q)d_1,r)<B(\epsilon,(1-q)d_2,r).$$
--
--   This is the comparative clause of the follower equilibrium's sufficient competition bound.
--
--   **Formalization Note** Increasing is interpreted strictly, in agreement with the positive derivatives in the proof. The payoff difference is parameterized directly, keeping $q,r$ fixed. The intrinsic representation is linked to (7) by the separate characterization item.
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, Online Appendix A p. 6 (PDF 39), Lemma O2

import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

namespace WangGreenTech.Regulation

open Set

theorem lemma_O2 (q r : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 < r) :
    (∀ d : ℝ, 0 < d → StrictMonoOn (fun ε => competitionBound ε ((1 - q) * d) r) (Ioi 0)) ∧
    (∀ ε : ℝ, 0 < ε → StrictMonoOn (fun d => competitionBound ε ((1 - q) * d) r) (Ioi 0)) := by sorry

end WangGreenTech.Regulation
