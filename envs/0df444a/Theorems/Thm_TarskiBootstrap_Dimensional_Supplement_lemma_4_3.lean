-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_lemma_4_3
-- name    : TarskiBootstrap.Dimensional.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:22.945081+00:00
-- url     : https://prove2.me/theorems/cad89eda-e518-4dbc-97ac-d227fef856f8
-- title:
--   Lemma 4.3 — Validity of the hidden-sign instances
-- statement:
--   Let $\mathcal F$ be a family of monotone self-maps of $[n]^k$, each with a unique fixed point $f^*$, whose possible fixed points lie on an antichain $A$, and let $D$ be the downward closure of $A$. Then for every $s\in\{-1,0,1\}$:
--
--   1. $H_s:f\mapsto(f,\sigma^f_s)$ is injective on $\mathcal F$;
--   2. for every $f\in\mathcal F$, the sign function $\sigma^f_s$ is monotone;
--   3. for every $f\in\mathcal F$, $f^*$ is the unique solution of the Tarski$^*$ instance $(f,\sigma^f_s)$: for all $x\in[n]^k$,
--   $$
--   \bigl(x\preceq f(x)\wedge\sigma^f_s(x)\ge0\bigr)\vee\bigl(x\succeq f(x)\wedge\sigma^f_s(x)\le0\bigr)\iff x=f^*.
--   $$
--
--   Here $\sigma^f_s$ equals $s$ at $f^*$, $-1$ at the other points of $D$ and $1$ off $D$. The lemma shows that $H_s(\mathcal F)$ consists of valid instances of the hidden-sign problem whatever sign is hidden.
--
--   Differences from the source:
--   - encoding: a hard instance family for Tarski(n, k) in which every function has a unique fixed point → F : Set (Grid n k → Grid n k) with every member monotone and having a unique fixed point; reason: Definition 2.1: instances are monotone self-maps of [n]^k; "hard" adds no assumption beyond the stated witness
--   - encoding: all possible fixed points lie on an antichain A → A antichain with possibleAnswers F ⊆ A; reason: literal transcription; the set of possible fixed points is the published possibleAnswers F
--   - encoding: s ∈ {−1, 0, 1} → s : SignType; reason: the same three ordered values
--   - encoding: f* is the unique solution → for all x, x is a solution ↔ x = fixedPoint f; reason: states both that f* solves the instance and that nothing else does; fixedPoint f is f* under uniqueness
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 4.3, PDF/printed pp. 17–18, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_HiddenSign
import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_TarskiStar

namespace TarskiBootstrap.Dimensional.Supplement

/-- Lemma 4.3, PDF/printed pp. 17–18: for every hidden sign `s ∈ {-1, 0, 1}`, the
hidden-sign constructor `H_s(f) = (f, σ_s^f)` is injective on `F`, each `σ_s^f` is
monotone, and `f*` is the unique solution of the `Tarski*` instance `(f, σ_s^f)`. -/
theorem lemma_4_3 {n k : ℕ+} (F : Set (Grid n k → Grid n k)) (A : Set (Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) A) (hcontains : possibleAnswers F ⊆ A)
    (s : SignType) :
    Function.Injective (fun f : F => (f.val, hiddenSign A s f.val)) ∧
    (∀ f : F, Monotone (hiddenSign A s f.val)) ∧
    (∀ f : F, ∀ x : Grid n k,
      IsTarskiStarSolution f.val (hiddenSign A s f.val) x ↔ x = fixedPoint f.val) := by sorry

end TarskiBootstrap.Dimensional.Supplement
