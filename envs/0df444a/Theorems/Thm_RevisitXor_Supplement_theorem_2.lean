-- Prove2me | Theorems.Thm_RevisitXor_Supplement_theorem_2
-- name    : RevisitXor.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:53:36.416847+00:00
-- url     : https://prove2.me/theorems/7d1a08e4-6072-4e65-96f9-5b28807b6dd1
-- title:
--   Theorem 2 — constant-factor XOR lemma with size at most $3s+5$
-- statement:
--   Let $f:[2]^n\to\{-1,1\}$ and let $C:[2]^n\times[2]^n\to\{-1,1\}$ be a fan-in-two Boolean circuit over the full binary basis with exactly $s$ gates. Suppose
--
--   $$
--   \mathbb E_{x,y\in[2]^n}[C(x,y)f(x)f(y)]\ge\epsilon.
--   $$
--
--   There is a unique real number $\alpha$ satisfying
--
--   $$
--   3\epsilon-\alpha^3=2\alpha,
--   $$
--
--   and there is a circuit $C':[2]^n\to\{-1,1\}$ of size at most $3s+5$ such that
--
--   $$
--   \mathbb E_{x\in[2]^n}[C'(x)f(x)]\ge\alpha.
--   $$
--
--   This is the paper's constant-factor form of the XOR lemma: nontrivial correlation with two copies yields controlled correlation with one copy at an exact additive gate overhead.
--
--   **Formalization Note** Sign-valued functions are represented by their bit exponents in $\mathbb F_2$, and both expectations are the published uniform signed correlation `RevisitXor.corr`. The two input blocks of $C$ are indexed by $\operatorname{Fin}(2)\times\operatorname{Fin}(n)$. Circuits use the published `AffDisp4n.Acyclic` full-basis $B_2$ syntax, whose size is its gate count.
--
--   Differences from the source:
--   - encoding: functions with values in $\{-1,1\}$ and their displayed uniform expectations → bit-valued functions over $\mathbb F_2$ and `RevisitXor.corr`; reason: $b\mapsto(-1)^b$ identifies the two encodings and preserves each displayed expectation
--   - encoding: a circuit on $[2]^n\times[2]^n$ → a full-basis $B_2$ circuit with inputs indexed by $\operatorname{Fin}(2)\times\operatorname{Fin}(n)$; reason: the two blocks are identified coordinate-for-coordinate and gate count is unchanged
--   - encoding: “$\alpha$ is the solution of $3\epsilon-\alpha^3=2\alpha$” → an existential $\alpha$ satisfying the equation together with explicit uniqueness; reason: this spells out the definite article in the source, and the cubic is strictly increasing after rearrangement
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Theorem 2, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Acyclic_eval

set_option autoImplicit false

namespace RevisitXor

namespace Supplement

/-- **Theorem 2 (constant-factor XOR lemma).** Viola, *Revisiting the XOR lemma*, STOC 2027
submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Theorem 2, p.3.

If a size-`s` fan-in-two Boolean circuit `C` has two-copy signed correlation at least `ε`
with `f`, then a circuit of size at most `3s + 5` has one-copy signed correlation at least
the unique real `α` satisfying `3ε - α³ = 2α`.

**Formalization Note.** The paper's sign-valued functions are encoded by bits in `ZMod 2`:
`sgn (f x)` is their value in `{1, -1}`. Thus the displayed expectations are exactly `corr`.
The two input blocks of `C` are indexed by `Fin 2 × Fin n`; block `0` receives `x` and block
`1` receives `y`. `AffDisp4n.Acyclic` is the published straight-line `B₂` circuit syntax over
the full binary basis, and `C.size` is its gate count. Constants and output complementation are
free, as in that circuit interface. -/
theorem theorem_2 {n s : ℕ} (f : Cube n → ZMod 2)
    (C : AffDisp4n.Acyclic (Fin 2 × Fin n)) (ε : ℝ) (hsize : C.size = s)
    (hcorr : ε ≤ corr
      (fun xy : Cube n × Cube n ↦
        C.eval (fun ji ↦ if ji.1 = 0 then xy.1 ji.2 else xy.2 ji.2))
      (fun xy ↦ f xy.1 + f xy.2)) :
    ∃ α : ℝ, 3 * ε - α ^ 3 = 2 * α ∧
      (∀ β : ℝ, 3 * ε - β ^ 3 = 2 * β → β = α) ∧
      ∃ C' : AffDisp4n.Circuit n, C'.size ≤ 3 * s + 5 ∧ α ≤ corr C'.eval f := by sorry

end Supplement

end RevisitXor
