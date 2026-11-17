-- Prove2me | Theorems.Thm_RevisitXor_Supplement_theorem_5
-- name    : RevisitXor.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:54:40.990632+00:00
-- url     : https://prove2.me/theorems/2ea5d6be-7c85-467b-b0f9-0737b533f892
-- title:
--   Theorem 5 — XOR lemma with quadratic loss in $1/\epsilon$
-- statement:
--   There is a positive absolute constant $c$ with the following property. Let $0<\epsilon\le 1/2$, let $f:[2]^n\to\{-1,1\}$, and let $C:[2]^n\times[2]^n\to\{-1,1\}$ be a fan-in-two Boolean circuit over the full binary basis of size at most $s$. If
--
--   $$
--   \mathbb E_{x,y\in[2]^n}[C(x,y)f(x)f(y)]\ge 3\epsilon^2,
--   $$
--
--   then there is a circuit $C':[2]^n\to\{-1,1\}$ such that
--
--   $$
--   \operatorname{size}(C')\le c\epsilon^{-2}\log(1/\epsilon)\,s
--   \qquad\text{and}\qquad
--   \mathbb E_{x\in[2]^n}[C'(x)f(x)]>\epsilon.
--   $$
--
--   This is the paper's quadratic-loss alternative proof of the XOR lemma; it retains both the factor $3$ in the hypothesis and the strict correlation improvement in the conclusion.
--
--   **Formalization Note** `Real.log` is the natural logarithm. Sign-valued functions are represented by their bit exponents in $\mathbb F_2$, and both displayed expectations are `RevisitXor.corr`. The two input blocks use $\operatorname{Fin}(2)\times\operatorname{Fin}(n)$, and circuits use the published full-basis $B_2$ syntax with gate-count size.
--
--   Differences from the source:
--   - encoding: sign-valued functions, uniform expectations, and a circuit on $[2]^n\times[2]^n$ → bit-valued functions, `RevisitXor.corr`, and a full-basis $B_2$ circuit indexed by $\operatorname{Fin}(2)\times\operatorname{Fin}(n)$; reason: the sign/bit and two-block identifications preserve the functions, expectations, and gate count
--   - encoding: $\log(1/\epsilon)$ with unspecified base → `Real.log (1 / ε)`, the natural logarithm; reason: changing the logarithm base only rescales the existential positive absolute constant
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Theorem 5, p.4, proof p.5 (PDF pp.4–5)

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Acyclic_eval

set_option autoImplicit false

namespace RevisitXor

namespace Supplement

/-- **Theorem 5 (quadratic-loss XOR lemma).** Viola, *Revisiting the XOR lemma*, STOC 2027
submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Theorem 5, pp.4–5.

There is a positive absolute constant `c` such that, for `0 < ε ≤ 1/2`, a circuit of size
at most `s` with two-copy correlation at least `3ε²` yields a one-copy circuit of size at
most `c · ε⁻² · log(1/ε) · s` whose correlation is strictly greater than `ε`.

**Formalization Note.** `Real.log` is the natural logarithm; changing the logarithm base only
rescales the existential absolute constant. The paper's sign-valued functions are represented
by their bit exponents in `ZMod 2`, so both displayed expectations are the published signed
uniform `corr`. The two blocks of the input circuit are indexed by `Fin 2 × Fin n`, and sizes
are gate counts in the published full-basis `B₂` circuit syntax. -/
theorem theorem_5 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n s : ℕ) (ε : ℝ) (f : Cube n → ZMod 2)
        (C : AffDisp4n.Acyclic (Fin 2 × Fin n)),
        0 < ε → ε ≤ 1 / 2 → C.size ≤ s →
        3 * ε ^ 2 ≤ corr
          (fun xy : Cube n × Cube n ↦
            C.eval (fun ji ↦ if ji.1 = 0 then xy.1 ji.2 else xy.2 ji.2))
          (fun xy ↦ f xy.1 + f xy.2) →
        ∃ C' : AffDisp4n.Circuit n,
          (C'.size : ℝ) ≤ c * (ε⁻¹) ^ 2 * Real.log (1 / ε) * (s : ℝ) ∧
          ε < corr C'.eval f := by sorry

end Supplement

end RevisitXor
