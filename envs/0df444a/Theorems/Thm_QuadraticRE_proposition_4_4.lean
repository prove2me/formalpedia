-- Prove2me | Theorems.Thm_QuadraticRE_proposition_4_4
-- name    : QuadraticRE.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:11:32.058764+00:00
-- url     : https://prove2.me/theorems/e2425f0f-a5b6-439e-84cf-dd781baadfe0
-- title:
--   Proposition 4.4 — privacy: $\mathrm{SD}\le5^{-2^{j-4}}+\frac1220^{-2^{j-4}}\le\frac325^{-2^{j-4}}$
-- statement:
--   There is a universal constant $K$ such that for all integers $j\ge4$, $h\ge3$, with $L=4^j$, the simulator $\mathrm{Sim}_{j,h}(y)=E_{j,h}(0,0,0,y;R')$ is computed by a straight-line program over $\mathbb F_2$ of at most $K\,Lh$ gates, and for every $(a,b,c,d)\in\mathbb F_2^4$
--   $$\mathrm{SD}\bigl(E_{j,h}(a,b,c,d;R),\mathrm{Sim}_{j,h}(abc+d)\bigr)\le5^{-2^{j-4}}+\tfrac12\,20^{-2^{j-4}}\le\tfrac32\,5^{-2^{j-4}} .$$
--
--   With Proposition 4.3 this makes $E_{j,h}$ a statistical encoding of $abc+d$ of degree two.
--
--   Differences from the source:
--   - generalization: there exists a randomized simulator Sim_{j,h} → the simulator E_{j,h}(0,0,0,y;R′) of the proof, named; reason: naming the witness implies the existence on the page
--   - reading: using O(Lh) operations → a straight-line program of at most K·L·h gates on (y, R′), one universal K; reason: the page counts field operations and names no machine; an SLP pays for each operation and has no branching, so this is the strong reading (paper.md decision 3)
--   - encoding: 5^{−2^{j−4}}, 20^{−2^{j−4}} → (1/5)^(2^(j−4)), (1/20)^(2^(j−4)) with j ≥ 4; reason: Lean notation; same numbers
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Proposition 4.4, p.20

import Mathlib
import Definitions.Def_QuadraticRE_encE
import Definitions.Def_QuadraticRE_SLP

namespace QuadraticRE

/-- Proposition 4.4 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.20: privacy of `E_{j,h}`, both inequalities.

**Formalization Note.** The simulator is named: it is the `Sim_{j,h}` of the proof, which implies the
existence on the page. It uses `O(Lh)` operations with one universal `K`: a straight-line program of
that size on `(y, R′)`. `5^{−2^{j−4}}` is written `(1/5)^(2^(j-4))`, with `j ≥ 4`. -/
theorem proposition_4_4 :
    ∃ K : ℕ, ∀ j h : ℕ, 4 ≤ j → 3 ≤ h →
      (∃ S : SLP (Unit ⊕ Fin (rho j h)) (Fin (4 ^ j) × Fin h × Fin 3),
        S.size ≤ K * (4 ^ j * h) ∧
        ∀ (y : F2) (R : Tape j h) (t : Fin (4 ^ j) × Fin h × Fin 3),
          S.eval (Sum.elim (fun _ => y) R) t = simE j h y R t.1 t.2.1 t.2.2) ∧
      ∀ a b c d : F2,
        SD (law (encE j h a b c d)) (law (simE j h (a * b * c + d)))
          ≤ (1 / 5 : ℝ) ^ (2 ^ (j - 4)) + (1 / 2) * (1 / 20 : ℝ) ^ (2 ^ (j - 4)) ∧
        (1 / 5 : ℝ) ^ (2 ^ (j - 4)) + (1 / 2) * (1 / 20 : ℝ) ^ (2 ^ (j - 4))
          ≤ (3 / 2) * (1 / 5 : ℝ) ^ (2 ^ (j - 4)) := by sorry

end QuadraticRE
