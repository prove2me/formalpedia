-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_20_4_3
-- name    : WildeQIT.Compression.Supplement.theorem_20_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:17:41.29589+00:00
-- url     : https://prove2.me/theorems/cd946bf6-0020-4241-b93d-e7fcba3d48d3
-- title:
--   Theorem 20.4.3 (Classical Capacity of the Depolarizing Channel): $C(\mathcal N_D)=\chi(\mathcal N_D)=\log d+(1-p+\frac pd)\log(1-p+\frac pd)+(d-1)\frac pd\log\frac pd$
-- statement:
--   Let $\mathcal N_D(\rho)=(1-p)\rho+p\pi$ be the depolarizing channel on a $d$-dimensional system, $p\in[0,1]$, $\pi=I/d$. Then its classical capacity and its Holevo information are both equal to
--
--   $$
--   \log d+\Big(1-p+\frac pd\Big)\log\Big(1-p+\frac pd\Big)+(d-1)\frac pd\log\frac pd ,
--   $$
--
--   with logarithms in base 2 and the convention $0\log0=0$.
--
--   The formula is $\log d-H_{\min}(\mathcal N_D)$: the output of every pure input has eigenvalues $1-p+\frac pd$ (once) and $\frac pd$ ($d-1$ times).
--
--   **Formalization Note** The classical capacity is the published `WildeQIT.ErasureClassical.classicalCapacity` (the extended-real supremum of achievable rates, §20.2.1) and $\chi$ the published `WildeQIT.Degradable.holevoInfoChannel`.
--
--   Differences from the source:
--   - reading: "The classical capacity of the qudit depolarizing channel N_D is as follows: χ(N_D) = …" → both the classical capacity C(N_D) and the Holevo information χ(N_D) equal the formula; reason: the sentence names the capacity and displays χ; the proof (King's additivity, then the χ computation) establishes both, so the stronger conjunction is stated
--   - encoding: a qudit system → `0 < d`; reason: a zero-dimensional system has no state; the hypothesis excludes only that case
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 20.4.3, p. 577, eq. (20.99); §20.4.4, p. 576, eq. (20.98)

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_depolarizingChannel
import Definitions.Def_WildeQIT_Degradable_holevoInfoChannel
import Definitions.Def_WildeQIT_ErasureClassical_classicalCapacity

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 20.4.3, p. 577.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 20.4.3 (Classical Capacity of the Depolarizing Channel)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 577, (20.99)):
"The classical capacity of the qudit depolarizing channel `N_D` is as follows:
`χ(N_D) = log d + (1 − p + p/d) log(1 − p + p/d) + (d − 1)(p/d) log(p/d)`."

Formalization Note: the theorem says "the classical capacity … is as follows" and displays
`χ(N_D)`; both readings are asserted: the classical capacity `C(N_D)` (the published
`WildeQIT.ErasureClassical.classicalCapacity`, the `EReal` supremum of achievable rates, §20.2.1)
equals the formula, and the Holevo information `χ(N_D)` (published
`WildeQIT.Degradable.holevoInfoChannel`, Definition 13.3.1) equals it. `N_D` is
`depolarizingChannel d p`, `ρ ↦ (1 − p)ρ + pπ` on `Fin d`, `p ∈ [0, 1]`, `d ≥ 1`. Logarithms are
base 2, and `0 log 0 = 0` (at `p = 0` the last term vanishes) because `Real.logb 2 0 = 0`. -/
theorem theorem_20_4_3 (d : ℕ) (hd : 0 < d) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    WildeQIT.ErasureClassical.classicalCapacity (depolarizingChannel d p h0 h1) =
        ((Real.logb 2 d + (1 - p + p / d) * Real.logb 2 (1 - p + p / d) +
          ((d : ℝ) - 1) * (p / d) * Real.logb 2 (p / d) : ℝ) : EReal) ∧
      WildeQIT.Degradable.holevoInfoChannel (depolarizingChannel d p h0 h1) =
        Real.logb 2 d + (1 - p + p / d) * Real.logb 2 (1 - p + p / d) +
          ((d : ℝ) - 1) * (p / d) * Real.logb 2 (p / d) := by sorry

end WildeQIT.Compression.Supplement
