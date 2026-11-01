-- Prove2me | Theorems.Thm_WildeQIT_ErasureClassical_holevoInfo_tensorPower_erasure_le
-- name    : WildeQIT.ErasureClassical.holevoInfo_tensorPower_erasure_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:37:45.471663+00:00
-- url     : https://prove2.me/theorems/e733b489-94a9-4628-b420-7f18abc482ab
-- title:
--   Proof of Theorem 20.4.2: $\chi((\mathcal N^\varepsilon)^{\otimes n})\le n(1-\varepsilon)\log d$
-- statement:
--   Let $d\ge1$, $\varepsilon\in[0,1]$ and let $\mathcal N^\varepsilon$ be the $d$-dimensional erasure channel. For every $n$,
--
--   $$
--   \chi\big((\mathcal N^\varepsilon)^{\otimes n}\big)\;\le\;n\,(1-\varepsilon)\log d ,
--   $$
--
--   so the regularized Holevo information $\chi_{\rm reg}(\mathcal N^\varepsilon)$ cannot exceed $(1-\varepsilon)\log d$. Together with Theorem 20.3.1 this is the converse of Theorem 20.4.2.
--
--   **Formalization Note** The $n$ input systems are indexed by `Fin n → Fin d` and may be entangled. Logarithms are base 2.
--
--   Differences from the source:
--   - generalization: χ((N^ε)^⊗n) ≤ n (1 − ε) log d for the n of a code (n ≥ 1) → for every n : ℕ, including n = 0; reason: at n = 0 the channel acts on a one-dimensional space and both sides are 0; the statement specializes to every n ≥ 1
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 20.4.2, p. 576

import Definitions.Def_WildeQIT_ErasureClassical_holevoInfo
import Definitions.Def_WildeQIT_Degradable_tensorPower
import Definitions.Def_WildeQIT_ErasureClassical_erasureChannel

namespace WildeQIT.ErasureClassical

/-- **Proof of Theorem 20.4.2, p. 576** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8): "By setting `M = (N^ε)^{⊗[n−1]}` and iterating the above, we see that
`χ((N^ε)^{⊗n}) ≤ n (1 − ε) log d`, so that the regularized Holevo information cannot exceed
`(1 − ε) log d`."

**Formalization Note.** Stated for every `n : ℕ`; at `n = 0` the channel acts on a
one-dimensional space and both sides are `0`. `ε ∈ [0, 1]`, `d ≥ 1`; logarithms base 2. -/
theorem holevoInfo_tensorPower_erasure_le (d : ℕ) (hd : 0 < d) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (n : ℕ) :
    holevoInfo (WildeQIT.Degradable.tensorPower (erasureChannel d ε h0 h1) n) ≤ n * ((1 - ε) * Real.logb 2 d) := by sorry

end WildeQIT.ErasureClassical
