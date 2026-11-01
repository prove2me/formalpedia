-- Prove2me | Theorems.Thm_WildeQIT_Covering_lemma_A_0_2
-- name    : WildeQIT.Covering.lemma_A_0_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:35:53.725029+00:00
-- url     : https://prove2.me/theorems/47e6aff9-1382-44f4-ba09-23d83f3965f0
-- title:
--   Operator interval and trace norm (corrected: $\varepsilon\ge0$): $(1-\varepsilon)\omega\le\hat\omega\le(1+\varepsilon)\omega\Rightarrow\|\hat\omega-\omega\|_1\le\varepsilon$
-- statement:
--   **Lemma A.0.2.** Let $\hat\omega$ and $\omega$ be operators on a finite-dimensional Hilbert space with trace at most one, $\operatorname{Tr}\hat\omega\le1$ and $\operatorname{Tr}\omega\le1$. Let $\varepsilon\ge0$ and suppose that $\hat\omega$ lies in the operator interval $[(1-\varepsilon)\omega,(1+\varepsilon)\omega]$, that is,
--
--   $$(1-\varepsilon)\,\omega\le\hat\omega\le(1+\varepsilon)\,\omega$$
--
--   in the operator (Loewner) order. Then
--
--   $$\|\hat\omega-\omega\|_1\le\varepsilon .$$
--
--   In the proof of the covering lemma it converts the operator Chernoff bound, which places the fake average inside an operator interval around the true average, into a bound on the trace distance.
--
--   **Formalization Note** "Trace at most one" is $\operatorname{Tr}\le1$ in the partial order of $\mathbb C$, so the traces are also real. $\|\cdot\|_1$ is the published trace norm without the factor $\tfrac12$.
--
--   Differences from the source:
--   - correction: no range for $\varepsilon$ → $\varepsilon\ge0$; reason: the printed claim is false for negative $\varepsilon$: $\hat\omega=\omega=0$ and $\varepsilon=-1$ satisfy every printed assumption, while $\|\hat\omega-\omega\|_1=0>-1$; the book uses the lemma only for $\varepsilon\in(0,1)$.
--   - encoding: the operator interval → positive semi-definiteness of $\hat\omega-(1-\varepsilon)\omega$ and $(1+\varepsilon)\omega-\hat\omega$; reason: definition of the Loewner order, as in (A.2), (A.3).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Appendix A, Lemma A.0.2, eq. (A.1), p. 739

import Definitions.Def_WildeQIT_traceNorm

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Covering

/-- **Lemma A.0.2** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Appendix A, eq. (A.1), p. 739). Suppose that the operators `ω̂` and `ω` have trace less than or
equal to one, and that `ω̂` lies in the operator interval `[(1 − ε)ω, (1 + ε)ω]`. Then
`‖ω̂ − ω‖₁ ≤ ε`.

**Formalization Note.** Operators on a finite-dimensional `H` are matrices over a finite index
type. "Trace less than or equal to one" is `Tr ω ≤ 1` in the order of `ℂ` (`ComplexOrder`), which
also says the trace is real. The operator interval is the Loewner order:
`(1 − ε)ω ≤ ω̂` and `ω̂ ≤ (1 + ε)ω` are `PosSemidef` differences. `‖·‖₁` is the published
unhalved `WildeQIT.traceNorm`.

**Correction.** The page states no range for `ε`; the hypothesis `0 ≤ ε` is added, because the
printed claim is false for negative `ε`: `ω̂ = ω = 0`, `ε = −1` satisfies every printed assumption
(`0 = (1 ± ε)·0`), while `‖ω̂ − ω‖₁ = 0 > −1`. The book applies the lemma only with `ε ∈ (0, 1)`. -/
theorem lemma_A_0_2 {n : Type} [Fintype n] [DecidableEq n]
    (ωhat ω : Matrix n n ℂ) (hωhat : ωhat.trace ≤ 1) (hω : ω.trace ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hlow : (ωhat - ((1 - ε : ℝ) : ℂ) • ω).PosSemidef)
    (hup : (((1 + ε : ℝ) : ℂ) • ω - ωhat).PosSemidef) :
    traceNorm (ωhat - ω) ≤ ε := by sorry

end WildeQIT.Covering
