-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_5_4_four_shears
-- name    : TransvectionMixing.lemma_5_4_four_shears
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:21:16.999087+00:00
-- url     : https://prove2.me/theorems/33da3b0f-7612-4cd0-aeeb-41c452ad795d
-- title:
--   Lemma 5.4 — four shears: a generic $W\in\mathrm{SL}_n$ factors as $\tilde U L(A)U(B)L(C)$
-- statement:
--   Assume $n\ge 256$. Over any field $K$, a generic $W\in\mathrm{SL}_n$ factors as
--   $$
--   W=\tilde U\,L(A)\,U(B)\,L(C),
--   $$
--   with every factor rational in $W$ over $K$. Here $L(\cdot)$, $U(\cdot)$ are the lower and upper shears for the split $B_0=\{1,\dots,\lfloor n/2\rfloor\}$, $B_1=\{\lfloor n/2\rfloor+1,\dots,n\}$, and $\tilde U$ is a shear from $B_1\setminus\{n\}$ to $B_0\cup\{n\}$.
--
--   The four-shear factorization is the target that a skeleton realizes segment by segment (Lemma 5.6).
--
--   **Formalization Note** "Generic $W$, factors rational in $W$" is an identity over the function field $K(\mathrm{SL}_n)$: the generic matrix $(x_{ij})$ equals $\tilde U L(A)U(B)L(C)$ with all blocks in $K(\mathrm{SL}_n)$.
--
--   Differences from the source:
--   - encoding: a generic W ∈ SLₙ factors with every factor rational in W → existence of Ũ, A, B, C over the function field K(SLₙ) with the generic matrix = Ũ L(A) U(B) L(C) and Ũ of the prescribed form; reason: rational functions of W are elements of K(SLₙ); an identity there holds on a nonempty open set
--   - encoding: blocks indexed by B₀ = {1, …, ⌊n/2⌋}, B₁, last row n → 0-based rows i < ⌊n/2⌋ and i ≥ ⌊n/2⌋, last row n − 1; reason: Lean indexing; same matrices
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 5.4, p.25 (standing assumption n ≥ 256 of §5.3, p.25)

import Mathlib
import Definitions.Def_TransvectionMixing_HasRationalSectionSL
import Definitions.Def_TransvectionMixing_MatchingCond

namespace TransvectionMixing

/-- **Lemma 5.4** (four shears) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §5.3.1, p.25). Assume `n ≥ 256` (standing in §5.3). Over
any field `K`, a generic `W ∈ SLₙ` factors as `W = Ũ L(A) U(B) L(C)`, with every factor
rational in `W` over that field. Here `L(A) = [[I_{⌊n/2⌋}, 0], [A, I_{⌈n/2⌉}]]`,
`U(B) = [[I_{⌊n/2⌋}, B], [0, I_{⌈n/2⌉}]]` for the split `B₀ = {1, …, ⌊n/2⌋}`,
`B₁ = {⌊n/2⌋ + 1, …, n}`, and `Ũ` is a shear from `B₁ ∖ {n}` to `B₀ ∪ {n}`.

**Formalization Note** "Generic `W`, factors rational in `W`" is an identity of matrices over
the function field `K(SLₙ)`: the generic matrix equals `Ũ L(A) U(B) L(C)` with all blocks in
`K(SLₙ)`. Only the off-diagonal blocks of `A, B, C` enter. -/
theorem lemma_5_4_four_shears (K : Type*) [Field K] (n : ℕ) (hn : 256 ≤ n) :
    ∃ U A B C : Matrix (Fin n) (Fin n) (SLFunctionField K n), IsModShear U ∧
      genericSL K n = U * lowerShear A * upperShear B * lowerShear C := by sorry

end TransvectionMixing
