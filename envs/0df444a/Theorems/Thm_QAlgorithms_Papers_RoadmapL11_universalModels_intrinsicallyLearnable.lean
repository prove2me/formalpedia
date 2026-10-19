-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL11_universalModels_intrinsicallyLearnable
-- name    : QAlgorithms.Papers.RoadmapL11.universalModels_intrinsicallyLearnable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:34:59.096509+00:00
-- url     : https://prove2.me/theorems/5f9c352e-5a10-440c-bb9f-8507d816bb37
-- title:
--   Universal world models admit intrinsic learning from experiments
-- statement:
--   Fix a positive finite dimension $d$ and finite labelled sets $X,Y,Z,B$ of preparation actions, dynamics actions, measurement actions, and measurement outcomes. Let $\mathcal Q$ be any set of world models $W=(\{\rho_x\}_{x\in X},\{\mathcal E_y\}_{y\in Y},\{M_{zb}\}_{z\in Z,b\in B})$ on $\mathbb C^d$: every preparation is a density matrix, every dynamics action is a CPTP map, and each measurement is a POVM. The model class may be uncountable and may contain equivalent descriptions.
--
--   Suppose every $W\in\mathcal Q$ is universal: some preparation is pure; some finite collection of dynamics actions implements exact unitary channels whose representatives generate a dense subgroup of $\mathrm{SU}(d)$; and some measurement effect is not proportional to the identity. These witnessing actions and their physical descriptions are unknown and may vary between worlds. Mathematical inverses enter the generated subgroup; physical access to inverse actions is not assumed.
--
--   Then there exists a fixed family $(L_k)_{k\in\mathbb N}$ of finite classical experimental procedures, chosen before the unknown world. Each procedure adaptively chooses experiments that freshly prepare $\rho_x$, apply a finite word of the available dynamics actions, and measure one of the available POVMs. Its description output is denoted $\widehat W^{(k)}=(\{\widehat\rho_x^{(k)}\},\{\widehat{\mathcal E}_y^{(k)}\},\{\widehat M_{zb}^{(k)}\})$. For every $W\in\mathcal Q$, every $\epsilon>0$, and every $0<\delta<1$, there exists $k_0$ such that for all $k\ge k_0$ there is one unitary or anti-unitary gauge $\mathcal G$ satisfying
--   $$
--   \begin{aligned}
--   \Pr_W\!\left[\|\rho_x-\mathcal G(\widehat\rho_x^{(k)})\|_1\le\epsilon\right]&\ge1-\delta &&(x\in X),\\
--   \Pr_W\!\left[\|\mathcal E_y-\mathcal G\circ\widehat{\mathcal E}_y^{(k)}\circ\mathcal G^{-1}\|_\diamond\le\epsilon\right]&\ge1-\delta &&(y\in Y),\\
--   \Pr_W\!\left[\|M_{zb}-\mathcal G(\widehat M_{zb}^{(k)})\|_1\le\epsilon\right]&\ge1-\delta &&(z\in Z,\ b\in B).
--   \end{aligned}
--   $$
--   Here $\Pr_W$ is computed from the experimental outcome probabilities and internal classical randomization of $L_k$. A unitary gauge has the form $\mathcal G(A)=UAU^\dagger$; an anti-unitary gauge has the form $\mathcal G(A)=U\overline A U^\dagger$. The same gauge is fixed outside all three collections of probability clauses. Both norms are unhalved. The output estimates need not themselves be lawful quantum objects.
--
--   The result establishes learnability of all labelled operations from untrusted experiments under universality. It gives eventual accuracy for each world, with no uniform sample bound, polynomial complexity guarantee, or certified accuracy-based stopping rule.
--
--   **Formalization Note** The finite-action scope is explicit in Theorem D.1 (PDF p.21), although the main-text Theorem 2 does not explicitly restrict the action sets. The stage-indexed interpretation follows the precision-halving procedure in D.2 (p.23) and D.7 (p.33).
-- source:
--   Foundations for learning from noisy quantum experiments, arXiv:2204.13691v1, Theorem 2; formal restatement Theorem D.1 (PDF p.21), PDF p. 4. https://arxiv.org/abs/2204.13691v1 . PDF SHA-256: 6dd0ad755733bac2b8ceda48c3afc8c194a3b66b2607e8b878484ad6f18a6f22.

import Definitions.Def_QAlgorithms_Defs_IntrinsicWorldLearning
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapL11

open QAlgorithms.IntrinsicLearning

/-- Huang, Flammia, and Preskill, *Foundations for learning from noisy quantum experiments*,
arXiv:2204.13691v1, Theorem 2 (PDF p.4), formally restated as Theorem D.1 (PDF p.21).
For fixed finite action and outcome spaces and positive finite dimension, every model class
whose members are universal is intrinsically learnable in the sense of Definition C.5 (p.20).
The unknown universality witnesses remain inside each world. A single family of finite adaptive
experimental programs is chosen before the true world; its eventual per-world guarantees use
one common unitary or anti-unitary gauge outside the individual probability clauses, unhalved
trace norm for states and effects, and diamond norm for channels. The staged interpretation is
the precision-halving procedure of D.2 (p.23) and D.7, Eqs. (D109)--(D111) (p.33).
The finite-action scope follows D.1; the main-text statement does not explicitly impose it.
-/
theorem universalModels_intrinsicallyLearnable
    {d : ℕ} (hd : 0 < d) {X Y Z B : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype B]
    (Q : Set (WorldModel d X Y Z B))
    (hQ : ∀ W ∈ Q, IsUniversalWorld W) :
    IsIntrinsicallyLearnable Q := by sorry

end QAlgorithms.Papers.RoadmapL11
