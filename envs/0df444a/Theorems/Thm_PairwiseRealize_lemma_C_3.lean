-- Prove2me | Theorems.Thm_PairwiseRealize_lemma_C_3
-- name    : PairwiseRealize.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:49.535269+00:00
-- url     : https://prove2.me/theorems/b92c3b4e-c8cd-47b9-b1cc-a759d94dd2e1
-- title:
--   Lemma C.3, p.16 — the partial coloring terminates within $16s\lambda^2$ steps with displacement at most $258\lambda$
-- statement:
--   Let $16\le s\le m$ and $A\in\{0,1\}^{m\times s}$. For every run of $T$ steps:
--
--   1. $T\le16s\lambda^2$;
--   2. if more than $s/2$ coordinates of the last state are unfrozen, a further step exists;
--   3. for every row $r$, $\bigl|\langle A_r/\lceil\sqrt s\rceil,\,x^{(T)}-x^{(0)}\rangle\bigr|\le258\lambda$.
--
--   Items 1 and 2 together are the termination claim: no run is longer, and a run stops only when at least half of the coordinates are frozen.
--
--   Differences from the source:
--   - generalization: the partial coloring with rational start, direction and weights → every run of the §C.1 step specification, over the reals; reason: the rational implementation of §C.2 is one such run
--   - reading: "terminates within 16sλ² steps" → no run has more than 16sλ² steps, and from a state with more than s/2 unfrozen coordinates a step exists; reason: a procedure defined by a step relation terminates when it cannot run longer and cannot get stuck
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Lemma C.3, p.16 (PDF p.17); §C.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_PairwiseRealize_PartialColoring

namespace PairwiseRealize

open PartialColoring

/-- **Lemma C.3, p.16 (PDF p.17).** K. Shi, H. Sun, *Robust Exact Realization of Pairwise Boolean
Statistics*, STOC 2027 submission (manuscript sha256 62090516…): "Lemma C.3. The partial coloring
terminates within 16sλ² steps and has |⟨vᵢ, x^{(T)} − x^{(0)}⟩| ≤ 258λ for the original unsigned
normals." The procedure is the partial coloring of §C.1 (p.15): `m` binary rows, `s` active
variables, `16 ≤ s ≤ m`, `λ = ⌈√P0⌉`, `P0 = ⌈log₂(256M/s)⌉`, `M = 2m`.

For every `A ∈ {0,1}^{m×s}` with `16 ≤ s ≤ m` and every run of `T` steps:
1. `T ≤ 16sλ²`;
2. if more than `s/2` coordinates of the last state are unfrozen, a further step exists (the
   procedure does not get stuck, so with 1 it terminates);
3. for every row `r`, `|⟨A_r/⌈√s⌉, x(T) − x(0)⟩| ≤ 258λ`.

**Formalization Note** A run is any sequence of states satisfying the §C.1 step specification
(`PartialColoring.IsRun`), including the paper's rational implementation (§C.2). "Terminates within
16sλ² steps" is items 1 and 2 together: no run is longer, and a run stops only when at least half
of the coordinates are frozen. -/
theorem lemma_C_3 (m s : ℕ) (hs : 16 ≤ s) (hsm : s ≤ m) (A : Fin m → Fin s → Bool) (T : ℕ)
    (x : Fin (T + 1) → Fin s → ℝ) (w : Fin (T + 1) → Fin m × Bool → ℝ) (hrun : IsRun A T x w) :
    (T : ℝ) ≤ 16 * s * lam m s ^ 2 ∧
    (s < 2 * (unfrozen (x (Fin.last T))).card →
      ∃ x' w', ValidStep A (x (Fin.last T)) (w (Fin.last T)) x' w') ∧
    ∀ r : Fin m, |rowNormal A r ⬝ᵥ (x (Fin.last T) - x 0)| ≤ 258 * lam m s := by sorry

end PairwiseRealize
