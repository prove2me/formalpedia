-- Prove2me | Theorems.Thm_SetDefinedGraphs_Supplement_theorem_1_10
-- name    : SetDefinedGraphs.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:46:26.798211+00:00
-- url     : https://prove2.me/theorems/847ffee9-0e13-4493-9764-69de68bf431b
-- title:
--   Theorem 1.10 — for a uniformly random $f$, $\mathbb P(\vec{\mathcal S}_2\subseteq\vec{\mathcal X}_f)\to1$ as $d\to\infty$
-- statement:
--   Let $f:\{0,1\}^{d^2}\to\{0,1\}$ be chosen uniformly at random among all $2^{2^{d^2}}$ Boolean functions. Then
--   $$\lim_{d\to\infty}\mathbb P\bigl(\vec{\mathcal S}_2\subseteq\vec{\mathcal X}_f\bigr)=1,$$
--   where $\vec{\mathcal S}_2\subseteq\vec{\mathcal X}_f$ means that every 2-dimensional shift digraph is $(d,f)$-set-defined.
--
--   Since $\vec{\mathcal S}_2$ is triangle-free with unbounded chromatic number, the full set-defined class of a typical function is $\chi$-unbounded.
--
--   **Formalization Note** The probability under the uniform distribution is the number of functions $f$ with $\vec{\mathcal S}_2\subseteq\vec{\mathcal X}_f$ divided by the number of all functions; the limit is along $d\to\infty$ in $\mathbb N$.
--
--   Differences from the source:
--
--   - encoding: P(S⃗_2 ⊆ X⃗_f) for f uniform on the Boolean functions on d² variables → Nat.card {f // every 2-dim shift digraph is InX f} / Nat.card {all f}, as a real number, tending to 1 along Filter.atTop; reason: the uniform probability on a finite set is the counting ratio
--   - encoding: Boolean function f : {0,1}^{d²} → {0,1} of the variables q_{i,j} → f : (Fin d → Fin d → Bool) → Bool, coordinate i ↦ index i − 1; reason: a function of the d² variables is a function of their value matrix; same instances
--   - encoding: arc (u,w) iff f(Q_{u,w}) = 1 → arc (u,w) iff u ≠ w and f(Q_{u,w}) = 1; reason: the paper's digraphs are loopless (p.2, p.14); the realisation is the paper's loopless digraph
--   - encoding: classes of (finite) digraphs, closed under isomorphism → predicates W ↦ (Digraph W → Prop) on digraphs over arbitrary vertex types (InX, InY, InYPZ: isomorphic to a realisation over a finite V); reason: isomorphism-closed classes of finite digraphs; the paper's realisations are over finite V (p.2)
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), Theorem 1.10, p.5 (PDF p.7); restated p.82 (PDF p.84)

import Mathlib
import Definitions.Def_SetDefinedGraphs_Classes
import Definitions.Def_SetDefinedGraphs_Supplement_ChiBoundedness

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- **Theorem 1.10** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.5, PDF p.7; restated p.82, PDF p.84): let `f : {0,1}^{d²} → {0,1}` be chosen
uniformly at random. Then `lim_{d→∞} P(S⃗_2 ⊆ X⃗_f) = 1`.

**Formalization Note** The uniform distribution on the `2^{2^{d²}}` Boolean functions makes `P(S⃗_2 ⊆ X⃗_f)` the number of
functions `f` for which every 2-dimensional shift digraph is `(d, f)`-set-defined, divided by the number of all
functions. The limit is along `d → ∞` in `ℕ`. -/
theorem theorem_1_10 :
    Filter.Tendsto
      (fun d : ℕ =>
        (Nat.card {f : (Fin d → Fin d → Bool) → Bool //
            ContainsShiftDigraphs 2 (fun W G => InX (W := W) f G)} : ℝ) /
          (Nat.card ((Fin d → Fin d → Bool) → Bool) : ℝ))
      Filter.atTop (nhds 1) := by sorry

end SetDefinedGraphs.Supplement
