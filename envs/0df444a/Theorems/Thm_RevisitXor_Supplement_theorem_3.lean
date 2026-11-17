-- Prove2me | Theorems.Thm_RevisitXor_Supplement_theorem_3
-- name    : RevisitXor.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:54:09.48028+00:00
-- url     : https://prove2.me/theorems/1e693f19-d0ca-4557-baad-8162524d799a
-- title:
--   Theorem 3 — XOR lemma with $c\sqrt{1/\epsilon}$ circuit loss
-- statement:
--   There are positive absolute constants $c_{\mathrm{size}}$, $c_{\mathrm{power}}$, and $c_{\mathrm{range}}$ with the following property. Let $f:[2]^n\to\{-1,1\}$, let $C:[2]^n\times[2]^n\to\{-1,1\}$ be a fan-in-two Boolean circuit over the full binary basis with exactly $s$ gates, and let $0<\epsilon\le c_{\mathrm{range}}$. If
--
--   $$
--   \mathbb E_{x,y\in[2]^n}[C(x,y)f(x)f(y)]\ge\epsilon,
--   $$
--
--   then there is a circuit $C':[2]^n\to\{-1,1\}$ satisfying
--
--   $$
--   \operatorname{size}(C')\le c_{\mathrm{size}}\sqrt{1/\epsilon}\,s
--   \qquad\text{and}\qquad
--   \mathbb E_{x\in[2]^n}[C'(x)f(x)]\ge\epsilon^{1-c_{\mathrm{power}}}.
--   $$
--
--   The theorem improves the dependence of the circuit-size loss in this two-copy-to-one-copy XOR lemma to the square-root scale in $1/\epsilon$.
--
--   **Formalization Note** The real power is `Real.rpow`. Sign-valued functions are represented by their bit exponents in $\mathbb F_2$, and the displayed expectations are `RevisitXor.corr`. The two input blocks use $\operatorname{Fin}(2)\times\operatorname{Fin}(n)$, and circuits use the published full-basis $B_2$ syntax with gate-count size.
--
--   Differences from the source:
--   - encoding: the three printed occurrences of the possibly different absolute constant $c$ → separate constants $c_{\mathrm{size}}$, $c_{\mathrm{power}}$, and $c_{\mathrm{range}}$, each quantified before all problem data; reason: the paper's p.1 convention says every occurrence of $c$ may denote a different positive absolute constant
--   - encoding: “for all $\epsilon\le c$” after expressions containing $\sqrt{1/\epsilon}$ and $\epsilon^{1-c}$ → $0<\epsilon\le c_{\mathrm{range}}$ with the power interpreted by `Real.rpow`; reason: positivity is the ordinary implicit domain of the printed expressions
--   - encoding: sign-valued functions, uniform expectations, and a circuit on two copies → bit-valued functions, `RevisitXor.corr`, and a full-basis $B_2$ circuit indexed by $\operatorname{Fin}(2)\times\operatorname{Fin}(n)$; reason: the sign/bit and two-block identifications preserve the functions, expectations, and gate count
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Theorem 3, p.3 (proof continues p.4; PDF pp.3–4)

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Acyclic_eval

set_option autoImplicit false

namespace RevisitXor

namespace Supplement

/-- **Theorem 3 (power amplification with square-root circuit loss).** Viola, *Revisiting the
XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716),
Theorem 3, pp.3–4.

There are positive absolute constants such that, for every sufficiently small positive `ε`,
a size-`s` circuit with two-copy correlation at least `ε` yields a circuit of size at most
`c_size · sqrt (1/ε) · s` and one-copy correlation at least `ε^(1-c_power)`.

**Formalization Note.** The paper states that each occurrence of `c` may denote a different
positive absolute constant. Accordingly `cSize`, `cPower`, and `cRange` are separate and are
quantified before `n`, `f`, `C`, and `ε`. Positivity of `ε` is the implicit domain condition of
the printed `sqrt (1/ε)` and real power. The sign/bit encoding, uniform correlations, two-block
input indexing, and concrete `B₂` circuit model are the same as in Theorem 2. -/
theorem theorem_3 :
    ∃ cSize cPower cRange : ℝ, 0 < cSize ∧ 0 < cPower ∧ 0 < cRange ∧
      ∀ (n s : ℕ) (f : Cube n → ZMod 2) (C : AffDisp4n.Acyclic (Fin 2 × Fin n))
        (ε : ℝ), C.size = s → 0 < ε → ε ≤ cRange →
        ε ≤ corr
          (fun xy : Cube n × Cube n ↦
            C.eval (fun ji ↦ if ji.1 = 0 then xy.1 ji.2 else xy.2 ji.2))
          (fun xy ↦ f xy.1 + f xy.2) →
        ∃ C' : AffDisp4n.Circuit n,
          (C'.size : ℝ) ≤ cSize * Real.sqrt (1 / ε) * (s : ℝ) ∧
          Real.rpow ε (1 - cPower) ≤ corr C'.eval f := by sorry

end Supplement

end RevisitXor
