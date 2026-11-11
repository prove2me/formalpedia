-- Prove2me | Theorems.Thm_SymThrWires_Main_lemma_E_5
-- name    : SymThrWires.Main.lemma_E_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:17:29.950433+00:00
-- url     : https://prove2.me/theorems/9a48829b-43cc-44a9-8267-6765a680e4d1
-- title:
--   Lemma E.5 — two-score discrete tomography: under S(⌊(D′−1)/(L−1)⌋) ≥ L, residue push-forwards determine a function on a box of side ≤ L
-- statement:
--   Let $P$ be a nonempty finite set of primes, $D'=1+\sum_{p\in P}(p-1)$, $L\ge2$ and $q=\lfloor(D'-1)/(L-1)\rfloor$, and let $S(q)=\sum_{m=1}^q m\varphi(m)$. If $S(q)\ge L$, then a rational-valued function on $\mathbb Z^2$ supported on a given box with both sides at most $L$ is uniquely determined, among functions supported on that box, by its push-forwards $F_p$, $p\in P$:
--   $$F,F'\text{ supported on the box},\quad F_p=F'_p\ (p\in P)\ \Longrightarrow\ F=F'.$$
--
--   This is the uniqueness half of the paper's modular tomography theorem: exact residue counts of a pair of integer scores, for enough primes, pin down their joint distribution.
--
--   Differences from the source:
--   - encoding: a box with both sides at most L; uniquely determined among functions supported on the box → the product of integer intervals [a_i, a_i + side_i) with side_i ≤ L; any two finitely supported F, F' : (Fin 2 → ℤ) →₀ ℚ supported there with equal push-forwards for every p ∈ P are equal; reason: a side is the number of integer points; uniqueness is injectivity
--   - encoding: q = ⌊(D′ − 1)/(L − 1)⌋ → natural-number division (Dprime P − 1) / (L − 1); reason: D′ ≥ 1 and L ≥ 2, so this is the floor
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 53, Lemma E.5

import Mathlib
import Definitions.Def_SymThrWires_Main_Tomography

namespace SymThrWires.Main

/-- **Lemma E.5** (p. 53). Let `P` be a nonempty finite set of primes, `D′ = 1 + Σ_{p∈P}(p − 1)`,
`L ≥ 2` and `q = ⌊(D′ − 1)/(L − 1)⌋`. If `S(q) ≥ L`, then a rational-valued function on `Z²`
supported on a given box with both sides at most `L` is uniquely determined, among functions
supported on that box, by its push-forwards `F_p`, `p ∈ P`. -/
theorem lemma_E_5 (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime) (L : ℕ)
    (hL : 2 ≤ L) (hS : L ≤ totientSum ((Dprime P - 1) / (L - 1)))
    (a : Fin 2 → ℤ) (side : Fin 2 → ℕ) (hside : ∀ i, side i ≤ L)
    (F F' : (Fin 2 → ℤ) →₀ ℚ)
    (hF : ∀ u ∈ F.support, ∀ i, a i ≤ u i ∧ u i < a i + side i)
    (hF' : ∀ u ∈ F'.support, ∀ i, a i ≤ u i ∧ u i < a i + side i)
    (hpush : ∀ p ∈ P, ∀ ρ : Fin 2 → ZMod p, pushforward F p ρ = pushforward F' p ρ) :
    F = F' := by sorry

end SymThrWires.Main
