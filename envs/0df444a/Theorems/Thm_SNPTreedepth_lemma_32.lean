-- Prove2me | Theorems.Thm_SNPTreedepth_lemma_32
-- name    : SNPTreedepth.lemma_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:32.29796+00:00
-- url     : https://prove2.me/theorems/2fd778d8-74ad-440d-a85e-768447f162fd
-- title:
--   Lemma 32 — $R$ and $R^s$ have the same induced substructures on at most $p$ elements
-- statement:
--   Let $R$ be a relational structure with treedepth decomposition $T$ and let $s\ge p\ge1$. For every relational structure $W$ (of the signature of $R$) on at most $p$ elements,
--   $$
--   R \text{ contains an induced copy of } W \iff R^s \text{ contains an induced copy of } W,
--   $$
--   where $R^s$ is the $s$-multiplicity structure for $(R,T,p)$.
--
--   With heredity (Observation 15) this is what transfers satisfaction of $\varphi$ between $R$ and $R^s$ in Lemma 9.
--
--   Differences from the source:
--   - encoding: W a relational structure on at most p elements; R contains an induced substructure isomorphic to W → W on Fin m with 1 ≤ m ≤ p; an injective map preserving and reflecting all relations; reason: domains are non-empty (Definition 12); an induced embedding is an isomorphism onto its image
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Lemma 32, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_SNPTreedepth_ptype
import Definitions.Def_SNPTreedepth_mult

set_option autoImplicit false

namespace SNPTreedepth

/-- **Lemma 32** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.30 (PDF p.31)): "Let R be a relational structure with treedepth
decomposition T, and s ≥ p ≥ 1 integers. Then, for any relational structure W on at most p elements,
we have that R contains an induced substructure isomorphic to W if and only if R^s contains an
induced substructure isomorphic to W."

**Formalization Note** `R^s` is the `s`-multiplicity structure for `(R, T, p)`. `W` ranges over the
structures of the signature of `R` on `Fin m` with `1 ≤ m ≤ p` (domains are non-empty,
Definition 12). -/
theorem lemma_32 {σ : Signature} {V : Type*} [Fintype V] [LinearOrder V] [Nonempty V]
    (R : Structure σ V) (T : RootedForest V) (hT : IsTDDecomp R T) (p s : ℕ) (hp : 1 ≤ p)
    (hps : p ≤ s) (m : ℕ) (hm1 : 1 ≤ m) (hmp : m ≤ p) (W : Structure σ (Fin m)) :
    W.EmbedsInduced R ↔ W.EmbedsInduced (mult R T p s) := by sorry

end SNPTreedepth
