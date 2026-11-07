-- Prove2me | Theorems.Thm_SNPTreedepth_lemma_19
-- name    : SNPTreedepth.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:49.539212+00:00
-- url     : https://prove2.me/theorems/5b69af52-f370-4e08-b32b-daa7e25d1bde
-- title:
--   Lemma 19 — the number of vertex $p$-types is at most $g(h,p,|\varphi|)$
-- statement:
--   There is a computable function $g$ such that for every instance $(R,\varphi)$ of SNP Model Checking, every treedepth decomposition $T$ of $R$ of height $h$ and every integer $p\ge1$,
--   $$
--   \bigl|\{p\text{-type}(v) : v\in V(R)\}\bigr|\ \le\ g(h,p,|\varphi|).
--   $$
--
--   The bound on the number of types underlies every size bound of the algorithm: the size of $R^p$ (Lemma 28 (8)), the number of route patterns, and the enumeration of Theorem 11.
--
--   Differences from the source:
--   - encoding: an SNP sentence under the conventions of pp.15–16 (negations only before atoms, every R_j, x_i and E_i occurs, positive arities) → Sentence.WellFormed as a hypothesis, NNF built into the syntax; reason: the paper assumes these without loss of generality; they are part of what an SNP Model Checking instance is
--   - encoding: a computable function g of three arguments → Computable of the uncurried g on ℕ × ℕ × ℕ, chosen before every instance; reason: same statement
--   - encoding: distinct vertex p-types → distinct ptype codes (equal exactly when the types are equal); reason: representation of types
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Lemma 19, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_Sentence
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_SNPTreedepth_ptype

set_option autoImplicit false

namespace SNPTreedepth

/-- **Lemma 19** (Depian, Ganian, Greilhuber, Gründel, Wietheger, *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), p.18 (PDF p.19)): "There is a computable function g such that for any
instance (R, φ) of SNP Model Checking, any treedepth decomposition T of R of height h, and any
integer p ≥ 1 the number |{p-type(v) | v ∈ V(R)}| of distinct vertex p-types is bounded by
g(h, p, |φ|)."

**Formalization Note** "Computable" for a function of three arguments is `Computable` of its
uncurried form on `ℕ × ℕ × ℕ`. An instance of SNP Model Checking is a well-formed sentence `φ` and a
structure `R` of the signature of `φ` on a finite non-empty domain. Vertex `p`-types are compared
through their codes (`ptype`), which are equal exactly when the types are equal. -/
theorem lemma_19 :
    ∃ g : ℕ → ℕ → ℕ → ℕ, Computable (fun x : ℕ × ℕ × ℕ => g x.1 x.2.1 x.2.2) ∧
      ∀ (σ : Signature) (φ : Sentence σ), φ.WellFormed →
      ∀ (V : Type) [Fintype V] [Nonempty V] (R : Structure σ V) (T : RootedForest V),
        IsTDDecomp R T → ∀ p : ℕ, 1 ≤ p →
          (Finset.univ.image (ptype R T p)).card ≤ g T.height p φ.length := by sorry

end SNPTreedepth
