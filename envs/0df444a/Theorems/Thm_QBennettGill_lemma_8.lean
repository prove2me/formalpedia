-- Prove2me | Theorems.Thm_QBennettGill_lemma_8
-- name    : QBennettGill.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:11:22.437212+00:00
-- url     : https://prove2.me/theorems/e8747692-deaf-4d39-94ab-ff5bd6e28c04
-- title:
--   Lemma 8 — the image of a random function $\{0,1\}^n\to\{0,1\}^n$ has density $1-1/e$
-- statement:
--   For $O_n:\{0,1\}^n\to\{0,1\}^n$ let
--
--   $$p_{O_n}:=\Pr_{y\xleftarrow{\$}\{0,1\}^n}\big[\exists x\in\{0,1\}^n:O_n(x)=y\big]=\frac{|\mathrm{Image}(O_n)|}{2^n}.$$
--
--   There is a negligible function $\mathrm{negl}$ such that for every $n$,
--
--   $$\Pr_{O_n\leftarrow\mathcal O_n}\Big[p_{O_n}\in\big[(1-\tfrac1e)-\mathrm{negl}(n),\ (1-\tfrac1e)+\mathrm{negl}(n)\big]\Big]\ge1-\mathrm{negl}(n),$$
--
--   where $O_n$ is uniformly random. This is the $(1-1/e)$-density of a random oracle as a PRHF (Definition 6, item 1).
--
--   Differences from the source:
--   - reading: Fixed any n ∈ ℕ … There exists negligible function negl(·) → ∃ negl, Negligible negl ∧ ∀ n; reason: a negligible function of a single fixed n is meaningless
--   - encoding: Pr over O_n ← 𝒪_n → the fraction of all functions Str n → Str n; reason: 𝒪_n is the uniform distribution on these functions
-- source:
--   Liang, Yamakawa, Yung, Structured Quantum Hardness from Unstructured Assumptions, STOC 2027 submission (held manuscript, sha256 6464b75a…), Lemma 8, p.26 (PDF p.29)

import Definitions.Def_QBennettGill_Negligible
import Definitions.Def_QBennettGill_boxD0

set_option autoImplicit false

namespace QBennettGill

open BBBV.RandomOracle

open Classical in
/-- **Lemma 8** ([GIK+23, Lemma B.3]): there is a negligible `negl` such that for every `n`, a uniformly
random `O_n : {0,1}ⁿ → {0,1}ⁿ` satisfies `p_{O_n} ∈ [(1 − 1/e) − negl(n), (1 − 1/e) + negl(n)]` with
probability at least `1 − negl(n)`, where `p_{O_n} = Pr_{y ←$ {0,1}ⁿ}[∃x, O_n(x) = y] = |Image(O_n)|/2ⁿ`.

Liang, Yamakawa, Yung, *Structured Quantum Hardness from Unstructured Assumptions*,
STOC 2027 submission (held manuscript, sha256 6464b75a…), Lemma 8, p.26 (PDF p.29).

**Formalization Note.** "Fixed any n … there exists negligible function negl" is read `∃ negl, ∀ n`. -/
theorem lemma_8 : ∃ negl : ℕ → ℝ, Negligible negl ∧ ∀ n : ℕ,
    1 - negl n ≤
      ((Finset.univ.filter (fun On : Str n → Str n =>
          (1 - Real.exp (-1)) - negl n ≤
              ((imageSet On).card : ℝ) / (Fintype.card (Str n) : ℝ) ∧
            ((imageSet On).card : ℝ) / (Fintype.card (Str n) : ℝ) ≤ (1 - Real.exp (-1)) + negl n)).card : ℝ) /
        (Fintype.card (Str n → Str n) : ℝ) := by sorry

end QBennettGill
