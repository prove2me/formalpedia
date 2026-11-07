-- Prove2me | Theorems.Thm_RandOrderCSP_theorem_3_10
-- name    : RandOrderCSP.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:59.897632+00:00
-- url     : https://prove2.me/theorems/45d16229-9939-4533-ba5d-f2dfea2d6e97
-- title:
--   Theorem 3.10 — local algorithms for the basic LP [Yos11]
-- statement:
--   For all $k,D\in\mathbb N$, $\varepsilon>0$ and every finite alphabet $\Sigma$, there are $R\in\mathbb N$ and a deterministic function $v:\mathcal N_{D,R,\{0,1\}^{\Sigma^k}}\to[0,1]$ such that for every $k$-ary CSP instance $\Phi=(H,f)$ with alphabet $\Sigma$ and maximum degree $D$,
--
--   $$\Big|\mathbb E_{j\in\mathcal E_H}\big[v(\mathrm{type}_R(H,f,j))\big]-\mathrm{opt}^{LP}_\Phi\Big|\le\varepsilon.$$
--
--   So the LP value of a bounded-degree instance is an average of a local function of neighbourhood types.
--
--   Differences from the source:
--   - encoding: v : N_{D,R,{0,1}^{Σ^k}} → [0, 1] → v on all finite rooted classes with values in [0, 1]; reason: a function on the subset extends by 0 and only types of degree-at-most-D instances are evaluated
--   - encoding: finite alphabet Σ → [Nonempty Sig]; reason: the source maximizes over assignments into Σ
--   - encoding: every CSP instance → the edge set is nonempty; reason: the expectation over a uniform edge needs an edge (p.13)
--   - reading: maximum degree D → every vertex has degree at most D (MaxDegLE); reason: the type set N_{D,R,·} is "degree-at-most-D" (p.14); this reading covers the instances of maximum degree exactly D
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Theorem 3.10, p.15

import Mathlib
import Definitions.Def_RandOrderCSP_optLP
import Definitions.Def_RandOrderCSP_typeR

namespace RandOrderCSP

/-- **Theorem 3.10 (local algorithms for the basic LP [Yos11]).** Singer, Tulsiani, Velusamy, *A dichotomy
theorem for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256
3aca9d2f…), Theorem 3.10, p.15.

**Formalization Note.** `v` is a function on all finite rooted classes with values in `[0,1]`. A function
on `N_{D,R,{0,1}^{Σ^k}}` extends by `0` and the rest of the statement evaluates `v` only at types of
degree-`≤ D` instances, so this is the printed strength. `[Nonempty E]`: the average over edges needs an
edge (p.13). `[Nonempty Sig]` is decision 7. -/
theorem theorem_3_10 (k D : ℕ) (ε : ℝ) (hε : 0 < ε) (Sig : Type) [Fintype Sig] [DecidableEq Sig]
    [Nonempty Sig] :
    ∃ (R : ℕ) (v : RootedClass k ((Fin k → Sig) → Bool) → ℝ), (∀ N, 0 ≤ v N ∧ v N ≤ 1) ∧
      ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [Nonempty E] (Φ : CSP k Sig V E),
        Φ.H.MaxDegLE D →
          |(1 / (Fintype.card E : ℝ)) * ∑ j, v (typeR Φ.H Φ.f j R) - optLP Φ| ≤ ε := by sorry

end RandOrderCSP
