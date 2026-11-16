-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_Supplement_lemma_8_2
-- name    : STOC2027BoolCSP.Approximation.Supplement.lemma_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:33:20.208168+00:00
-- url     : https://prove2.me/theorems/fa80bf40-e534-472b-83b5-6c525af8c2d1
-- title:
--   Lemma 8.2 — deterministic Gaussian orthant integration at fixed dimension, uniform in the mean
-- statement:
--   Fix $m\ge 0$. There is a deterministic algorithm with the following guarantee. Its input is a rational vector $a\in\mathbb Q^m$, a rational symmetric $m\times m$ matrix $V$ with
--   $$V\succeq \tfrac14 I_m,\qquad V_{jj}\le 8\ \ (1\le j\le m),$$
--   a rational accuracy $0<\tau<1/2$, a sign pattern $s\in\{-1,1\}^m$ and a mode: either the orthant $O_s=\{x:\ s_jx_j\ge0\ \forall j\}$ or the antipodal pair $O_s\cup O_{-s}$. It outputs a rational $r$ with
--   $$\big|\,r-\Pr_{Y\sim N(a,V)}[Y\in E]\,\big|\le\tau,$$
--   $E$ the specified event, and its running time is at most $P(L+\lceil 1/\tau\rceil)$, where $L$ is the input bit length and $P$ is a polynomial depending only on $m$. The algorithm and the polynomial are the same for every mean $a$, so the error bound is uniform in $a$.
--
--   The lemma is the integration oracle of the deterministic implementation (Theorem 8.1): it evaluates every conditional clause probability (42), whose conditional means are nonzero.
--
--   Differences from the source:
--   - encoding: deterministic algorithm, polynomial in the rational input bit length and 1/τ with exponent depending only on m → one CoinMachine run on the empty random tape, halting within P(1 + L + ⌈1/τ⌉) steps, Mach and P chosen before a, V, τ, s and the mode; reason: the live mission's machine model; a deterministic computation is a run with no random bits
--   - encoding: the input (a, V, τ, specified orthant or pair) → the bit string integrationCode: listCode of the entries of a, sqMatCode V, ratCode τ, the m sign bits, one mode bit; output ratCode r; reason: explicit input bit length
--   - encoding: orthant → closed orthant {x : sgn(s_j) x_j ≥ 0 ∀ j}; reason: V ⪰ I/4 makes N(a, V) nondegenerate, so boundaries are null and open and closed orthants have the same probability
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 18–19 (PDF 21–22), Lemma 8.2 and its proof

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_Machine
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Integration

namespace STOC2027BoolCSP.Approximation.Supplement

open MeasureTheory ProbabilityTheory STOC2027BoolCSP.Approximation

/-- Lemma 8.2 (uniform integration at fixed dimension), printed p. 18. For every fixed `m` there
are one finite bit machine and one polynomial `P` (depending only on `m`) such that for every
rational mean `a ∈ ℚ^m`, every rational symmetric `V` with `V ⪰ I_m/4` and `V_jj ≤ 8`, every
rational `0 < τ < 1/2`, every sign pattern `s` and both modes (one orthant, or a pair of antipodal
orthants), the run on the input code with the empty random tape (a deterministic computation)
halts within `P(1 + L + ⌈1/τ⌉)` steps, `L` the input length, and outputs a rational within `τ`
of the `N(a, V)` probability of the event. -/
theorem lemma_8_2 (m : ℕ) :
    ∃ (Mach : CoinMachine) (P : Polynomial ℕ),
      ∀ (a : Fin m → ℚ) (V : Matrix (Fin m) (Fin m) ℚ) (τ : ℚ) (s : Fin m → Bool) (pair : Bool),
        V.IsSymm →
        (ratToReal V - (1 / 4 : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef →
        (∀ j, V j j ≤ 8) → 0 < τ → τ < 1 / 2 →
        ∃ r : ℚ,
          Mach.HaltsWithin (integrationCode a V τ s pair) []
            (P.eval (1 + (integrationCode a V τ s pair).length + ⌈1 / τ⌉₊)) (ratCode r) ∧
          |(r : ℝ) - (multivariateGaussian (ratVec a) (ratToReal V)).real (targetSet s pair)|
            ≤ τ := by sorry

end STOC2027BoolCSP.Approximation.Supplement
