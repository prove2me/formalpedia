-- Prove2me | Theorems.Thm_RudnevIncidence_PointPlane_lemma_9
-- name    : RudnevIncidence.PointPlane.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:44.73699+00:00
-- url     : https://prove2.me/theorems/5342fdaf-3440-4e59-adf5-6f2c644f3578
-- title:
--   Lemma 9, p. 12 — point-plane incidences in P³ become incidences between two families of mutually skew lines in a three-quadric
-- statement:
--   Let $\mathbb F$ be algebraically closed of characteristic $\neq2$, and let $P$ and $\Pi$ be finite sets of $m$ points and $n$ planes of $\mathbb P^3$. Then there is a hyperplane $S$ of $\mathbb P^5$, not tangent to the Klein quadric $\mathcal K$, such that the families
--   $$L_\alpha=\{\alpha(q)\cap S: q\in P\},\qquad L_\beta=\{\beta(\pi)\cap S:\pi\in\Pi\}$$
--   of α-lines and β-lines satisfy:
--
--   1. every member of $L_\alpha\cup L_\beta$ is a line of the three-quadric $\mathcal G=\mathcal K\cap S$;
--   2. $L_\alpha$ and $L_\beta$ are disjoint, and no two lines of the same family meet;
--   3. $|L_\alpha|=m$ and $|L_\beta|=n$;
--   4. $|I(P,\Pi)|=|I(L_\alpha,L_\beta)|$;
--   5. for every $k\in\mathbb N$: every line of $\mathbb P^3$ contains at most $k$ points of $P$ if and only if every projective three-subspace of $S$ contains at most $k$ lines of $L_\alpha$; and every line of $\mathbb P^3$ lies in at most $k$ planes of $\Pi$ if and only if every projective three-subspace of $S$ contains at most $k$ lines of $L_\beta$.
--
--   Item 5 says that the maximum numbers of collinear points and of collinear planes equal the maximum numbers of lines of $L_\alpha$, resp. $L_\beta$, in the intersection of $\mathcal G$ with a three-subspace of $S$. Combined with Theorem 12 this gives Theorem 3.
--
--   **Formalization Note** The families are constructed from $P$ and $\Pi$ as on the page: each point and each plane contributes the intersection of its α- or β-plane with $S$. A projective three-subspace of $S$ is a 4-dimensional subspace $V\subseteq S$ of $\mathbb F^6$, and a line of $\mathcal G$ lies in $\mathcal G\cap V$ iff it is contained in $V$. The equality of maxima is stated as an equivalence of upper bounds for every $k$, which avoids a supremum over the infinitely many lines of $\mathbb P^3$. The second paragraph of the lemma ("Alternatively, one can regard $S$ as fixed …") is a reformulation not used by Theorem 3 and is not part of this statement.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 12, §4.2, Lemma 9 (first and third paragraphs)

import Mathlib
import Definitions.Def_RudnevIncidence_PointPlane_Setting

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

theorem lemma_9 {F : Type*} [Field F] [IsAlgClosed F] (hF : ringChar F ≠ 2)
    (P Pl : Finset (ℙ F (Fin 4 → F))) :
    ∃ U : Fin 6 → F, NonTangent U ∧
      (∀ W ∈ P.image (alphaLine U), IsLineIn U W) ∧
      (∀ W ∈ Pl.image (betaLine U), IsLineIn U W) ∧
      Disjoint (P.image (alphaLine U)) (Pl.image (betaLine U)) ∧
      ((P.image (alphaLine U) : Set (Submodule F (Fin 6 → F))).Pairwise
        (fun W W' => W ⊓ W' = ⊥)) ∧
      ((Pl.image (betaLine U) : Set (Submodule F (Fin 6 → F))).Pairwise
        (fun W W' => W ⊓ W' = ⊥)) ∧
      (P.image (alphaLine U)).card = P.card ∧
      (Pl.image (betaLine U)).card = Pl.card ∧
      lineIncidences (P.image (alphaLine U)) (Pl.image (betaLine U)) = incidences P Pl ∧
      (∀ k : ℕ,
        (∀ W : Submodule F (Fin 4 → F), Module.finrank F W = 2 → (pointsOn P W).card ≤ k) ↔
        (∀ V : Submodule F (Fin 6 → F), V ≤ hyperplane U → Module.finrank F V = 4 →
          ((P.image (alphaLine U)).filter (· ≤ V)).card ≤ k)) ∧
      (∀ k : ℕ,
        (∀ W : Submodule F (Fin 4 → F), Module.finrank F W = 2 → (planesThrough Pl W).card ≤ k) ↔
        (∀ V : Submodule F (Fin 6 → F), V ≤ hyperplane U → Module.finrank F V = 4 →
          ((Pl.image (betaLine U)).filter (· ≤ V)).card ≤ k)) := by sorry
end RudnevIncidence.PointPlane
