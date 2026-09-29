-- Prove2me | Theorems.Thm_QFS_ref_cones_paper
-- name    : QFS.ref_cones_paper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-06T19:59:03.704297+00:00
-- url     : https://prove2.me/theorems/3321ead7-7078-4bd4-ae22-8f05cb644f4b
-- title:
--   Lemma 2.2 — finitely many reference cones, with the apex angle existentially quantified
-- statement:
--   **Lemma 2.2 of Bux–Kassmann–Schulze**, in the source's own shape. Fix a space and an angle
--   $0 < \vartheta \le \pi/2$. Then there are an angle $\theta \in (0, \pi/2]$ and a finite set
--   $S$ of unit vectors $v^1, \dots, v^L$ such that for **every** $\vartheta$-bounded
--   configuration $\Gamma$ and every $x$, some $V(v^m, \theta) \subseteq \Gamma(x)$.
--
--   **The family comes before the configuration**, which is the content of the lemma's last
--   sentence: "The constants $L$ and $\theta$ depend on the dimension $d$ and $\vartheta$ but not
--   on $\Gamma$ itself." The opening sentence — "Let $\Gamma$ be a $\vartheta$-bounded
--   configuration. There are numbers $L$ and $\theta$ …" — would on its own permit dependence on
--   $\Gamma$; the closing sentence rules it out, and that is the order used here. (The same
--   pattern recurs at Corollary 3.6, where Proposition 3.5's `C = C(d, ϑ)` fixes the reading.)
--
--   The proof is the source's: the open cover $\{V(v, \vartheta/3)\}_{v \in S^{d-1}}$ of the unit
--   sphere has a finite subcover, and $\theta = \vartheta/3$ works.
--
--   **The development pins $\theta = \vartheta/3$** rather than quantifying it, which is exactly
--   what the proof delivers and is therefore stronger; this statement is that one with the
--   existential restored. The development's form lives inside the published definition bundle
--   `QFS_RefCones`, because the family of reference cones
--   (Definition 2.3) is *defined* by choice from it, so it cannot also be a standalone theorem.
--   This restatement is what a milestone can point at.
--
--   Finite-dimensionality of the space is required and is a hypothesis here; the source works in
--   $\mathbb{R}^d$ throughout. The conclusion uses double cones, matching Definition 2.1.
-- source:
--   https://github.com/dbenbenn/quadratic-forms-sobolev/blob/7a1a680db2124d46ce370c91fd450aa454edf491/QuadraticFormsSobolev/RefCones.lean#L133-L148

import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric InnerProductGeometry

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem QFS.ref_cones_paper {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ ≤ π / 2) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ π / 2 ∧
      ∃ S : Finset E, (∀ v ∈ S, ‖v‖ = 1) ∧
        ∀ Γ : Configuration E, IsBounded Γ ϑ →
          ∀ x : E, ∃ v ∈ S, doubleCone v θ ⊆ (Γ x).carrier := by sorry
