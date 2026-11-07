-- Prove2me | Theorems.Thm_RSBDDHard_lemma_3_2
-- name    : RSBDDHard.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:43.113587+00:00
-- url     : https://prove2.me/theorems/169e4ec1-f4e4-4144-9a78-257593e4700c
-- title:
--   Lemma 3.2 — degree descent, Artin–Schreier descent, and the orbit product
-- statement:
--   Let $K\subseteq F=K(\gamma)$ be finite fields of characteristic $p$ with $[F:K]=E$, and write $\mathcal L(x)=x^p-x$.
--
--   1. If $z(T)\in K[T]$ has $\deg_T z<E$ and $z(\gamma)\in K$, then $z$ is constant. In particular, $z(\gamma)=0$ implies $z=0$.
--   2. If $p\nmid E$, $x\in F$ and $\mathcal L(x)\in K$, then $x\in K$.
--   3. For every $\lambda\in F$,
--   $$\prod_{a\in\mathbb F_p}\bigl(1-(\lambda+a)Z\bigr)=1-Z^{p-1}-\mathcal L(\lambda)Z^p.$$
--
--   Part 1 is the degree-separation tool; part 2 turns a condition in $K$ on $\mathcal L(x)$ into one on $x$; part 3 says that a complete additive orbit $\lambda+\mathbb F_p$ contributes nothing to the coefficients of $Z,\dots,Z^{p-2}$ of the reciprocal product.
--
--   Differences from the source:
--   - encoding: K ⊆ F, characteristic p → an algebra map K → F, "∈ K" as membership in its image, and an F_p-algebra structure on F; reason: Lean's representation of a subfield and of the characteristic; same instances
--   - generalization: §3 standing assumption (1), p.18, which gives p ≥ 5 → every prime p; reason: the lemma's own hypotheses are finite fields of characteristic p, and parts (i)–(iii) hold for every prime p (part (iii) also at p = 2); every p satisfying (1) is an instance
-- source:
--   Gandikota, Grigorescu, Venkitesh, NP-Hardness of Bounded Distance Decoding for Reed-Solomon Codes and Variants, via Non-Archimedean Rings, STOC 2027 submission (sha256 0372e933…), Lemma 3.2, pp.19–20

import Mathlib
import Definitions.Def_RSBDDHard_recipProd

set_option autoImplicit false

namespace RSBDDHard

open Polynomial

/-- **Lemma 3.2.** Gandikota, Grigorescu, Venkitesh, *NP-Hardness of Bounded Distance Decoding
for Reed-Solomon Codes and Variants, via Non-Archimedean Rings*, STOC 2027 submission (sha256
0372e933…), pp.19–20. Let `K ⊆ F = K(γ)` be finite fields of characteristic `p` with
`[F : K] = E`.

1. If `z(T) ∈ K[T]` has `deg z < E` and `z(γ) ∈ K`, then `z` is constant; in particular
   `z(γ) = 0` implies `z = 0`.
2. If `p ∤ E`, `x ∈ F` and `L(x) = x^p − x ∈ K`, then `x ∈ K`.
3. For every `λ ∈ F`, `Π_{a ∈ F_p} (1 − (λ + a)Z) = 1 − Z^{p−1} − L(λ)Z^p`.

**Formalization Note.** Characteristic `p` is an `F_p`-algebra structure on `F`; `K` embeds in
`F` by `algebraMap`, and "`∈ K`" means in its image. `F = K(γ)` is
`IntermediateField.adjoin K {γ} = ⊤`. `Polynomial.degree 0 = ⊥`, the paper's `deg 0 = −∞`. -/
theorem lemma_3_2 (p : ℕ) [Fact p.Prime] {K F : Type*} [Field K] [Field F] [Finite F]
    [Algebra K F] [Algebra (ZMod p) F] (E : ℕ) (γ : F)
    (hγ : IntermediateField.adjoin K {γ} = ⊤) (hE : Module.finrank K F = E) :
    (∀ z : K[X], z.degree < E → aeval γ z ∈ Set.range (algebraMap K F) → ∃ c : K, z = C c) ∧
    (∀ z : K[X], z.degree < E → aeval γ z = 0 → z = 0) ∧
    (¬ p ∣ E → ∀ x : F, artinSchreier p x ∈ Set.range (algebraMap K F) →
      x ∈ Set.range (algebraMap K F)) ∧
    (∀ l : F, ∏ a : ZMod p, (1 - C (l + algebraMap (ZMod p) F a) * X) =
      1 - X ^ (p - 1) - C (artinSchreier p l) * X ^ p) := by sorry

end RSBDDHard
