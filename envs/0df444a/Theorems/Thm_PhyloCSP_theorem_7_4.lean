-- Prove2me | Theorems.Thm_PhyloCSP_theorem_7_4
-- name    : PhyloCSP.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:53.605272+00:00
-- url     : https://prove2.me/theorems/c34c7c9d-edb4-4ff4-8191-2b26bc0b9ebe
-- title:
--   Theorem 7.4 — existence and uniqueness of the Fraïssé limit
-- statement:
--   There exists a Fraïssé limit of finite binary tree structures, and it is unique up to isomorphism. Concretely: the structure $(Z,C)$ of Definition 7.5 (finite sets of rationals, with the rooted-triplet relation of eq. (5)) is a Fraïssé limit, and every Fraïssé limit $(X,C_X)$ of finite binary tree structures is isomorphic to it, i.e. there is a bijection $e:X\to Z$ with
--   $$
--   C_X(a;b,c)=C\bigl(e(a);e(b),e(c)\bigr)\qquad\text{for all }a,b,c\in X .
--   $$
--
--   The rest of the paper works on this universal homogeneous structure $\mathcal F$: random relations on it play the role of tree transformations.
--
--   Differences from the source:
--   - generalization: there exists a Fraïssé limit → the concrete structure (Z, C) of Definition 7.5 is a Fraïssé limit; reason: Appendix B.1 identifies the concrete structure with F; a concrete witness implies existence
--   - encoding: finite binary tree structures; domains of arbitrary structures → patterns on Fin n; domains X : Type; reason: every finite binary tree structure is isomorphic to one on Fin n
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 7.4, p.19 (PDF p.21); Definition 7.5, p.20 (PDF p.22); Appendix B.1, pp.44–45 (PDF pp.46–47)

import Mathlib
import Definitions.Def_PhyloCSP_IsFraisseLimit
import Definitions.Def_PhyloCSP_fraisseRel

set_option autoImplicit false

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Theorem 7.4, p.19 (PDF p.21): "There exists a
Fraïssé limit of finite binary tree structures. Further, it is unique up to isomorphism." With
Definition 7.5, p.20 (PDF p.22) and Appendix B.1, pp.44–45 (PDF pp.46–47): "Thus the
correspondence above identifies our leaf structure with F under our convention."

Existence is witnessed by the concrete structure `(Z, fraisseRel)` of Definition 7.5; uniqueness:
every Fraïssé limit `(X, C)` is isomorphic to it.

**Formalization Note.** Isomorphisms preserve truth and falsity of the relation (Definition 7.2).
The domains `X` range over `Type`. -/
theorem theorem_7_4 :
    IsFraisseLimit Z fraisseRel ∧
      ∀ (X : Type) (C : X → X → X → Bool), IsFraisseLimit X C →
        ∃ e : X ≃ Z, ∀ a b c, C a b c = fraisseRel (e a) (e b) (e c) := by sorry

end PhyloCSP
