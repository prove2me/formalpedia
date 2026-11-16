-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_corollary_4_10
-- name    : RoundedPotentials.Main.Supplement.corollary_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:10:49.641739+00:00
-- url     : https://prove2.me/theorems/53867720-cffd-4861-bd88-0035d8533c7a
-- title:
--   Corollary 4.10 — Global all-pairs verification
-- statement:
--   Fix an exponent $D$ and $\varepsilon>0$, and let $\gamma$ be as in Corollary 4.9. There are a deterministic word-RAM program $V$ and constants $C,K$ that form a **nondeterministic algorithm for a total function** (Definition 2.3) computing the ordered-pair maximum-flow matrix of directed graphs. The input is $n\ge2$ and a capacity matrix with entries at most $W\le n^D$. Let $T=Cn^{\gamma+\varepsilon}+C$. Then:
--
--   1. for every guess $g$, $V(x,g)$ halts within $T$ steps;
--   2. for every guess $g$, $V(x,g)$ outputs either "don't know" or a matrix $M$ with $M_{uv}=\mathrm{MaxFlow}(u,v)$ for all $u\ne v$;
--   3. for at least one guess, $V(x,g)$ outputs that matrix.
--
--   Algorithm 1 is such an algorithm, so the running time is $n^{\gamma+o(1)}$.
--
--   **Formalization Note** Machine: `DynConnWC.Program` with `MinKCutII_Main_Runs`. The guess is read after the instance, and the word size depends only on the instance. "Don't know" is the output $[0]$, and a solution is $1$ followed by the matrix row by row.
--
--   Differences from the source:
--   - reading: Algorithm 1 is a nondeterministic algorithm … with running time n^{γ+o(1)} → for every ε > 0 there is a deterministic word-RAM program V with NondetAPMF at time C·n^{γ+ε} + C; reason: Algorithm 1 leaves the multiplication routine open; for each ε its instance with a suitable routine is such a program
--   - generalization: γ with the exponent ω(a, b, c) → γ with the published operational exponent omega3; reason: the operational exponent is at most the algebraic one, so the bound with this γ implies the source's
--   - encoding: Definition 2.3 (running time T for every guess, a solution or don't know, a solution for some guess) → NondetAPMF: on input n and the capacity matrix followed by the guess, halts within T, outputs [0] or 1 followed by a matrix of maximum-flow values off the diagonal; some guess outputs such a matrix; reason: same notion; the guess cannot enlarge the word size
--   - reading: directed graphs (with capacities) → capacity matrices with entries ≤ W ≤ n^D, diagonal ignored, for every fixed D; reason: the standing polynomial bound of §1.1; §2 graphs are loopless
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 24, Corollary 4.10

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Verification

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main DynConnWC MinKCutII.Main MultStretchAPASP.Weighted

theorem corollary_4_10 (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Program) (C K : ℕ),
      ∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → W ≤ n ^ D →
      ∀ (cap : Fin n → Fin n → ℕ), (∀ u v, cap u v ≤ W) →
        NondetAPMF P K n W cap (C * (n : ℝ) ^ (gammaExp + ε) + C) := by sorry

end RoundedPotentials.Main.Supplement
