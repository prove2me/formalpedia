-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_D_5
-- name    : SparseWalsh.Approx.lemma_D_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:04:26.106888+00:00
-- url     : https://prove2.me/theorems/8c1b3b1c-9d3b-4ea4-8412-8e6a9172a3ea
-- title:
--   Lemma D.5 — final coefficient estimates are accurate to ρ_j on all of W with probability at least 63/64
-- statement:
--   Let $d\ge1$, $1\le s\le2^d$, $0<\varepsilon\le1$ and $0<\beta\le1/8$. Let $T$ be the support of an optimal $s$-term approximation of $f:\mathbb F_2^d\to\mathbb R$, and $\tau^2=\sum_{a\notin T}\hat f(a)^2$. The final estimation list $E_{\rm fin}$ of Algorithm 3 consists of $q_{\rm fin}=\lceil8\ln(64U)\rceil$ independent uniform pairs $(C,y)$ whose tables have $P_{\rm fin}$ buckets, with the parameters of (9). Let $W$ be a candidate set with $|W|\le U$ that is independent of these tables. Then with probability at least $63/64$ every $a\in W$ satisfies
--   $$\big|\mathrm{Est}_{E_{\rm fin}}(\hat f,a)-\hat f(a)\big|\le\rho_j,\qquad \rho_j=\begin{cases}\varepsilon\tau/(16\sqrt s), & j=s,\\ \sqrt\varepsilon\,\tau/(4\sqrt s), & j=2s.\end{cases}$$
--   When $\tau=0$, all these estimates are exact on this event. Together with Lemma 5.2 and Lemma D.4 this gives the approximation guarantee of Theorem 5.1.
--
--   Differences from the source:
--
--   - reading: a random candidate set W with |W| ≤ U, independent of the final estimation tables → every fixed W with |W| ≤ U; reason: a W independent of the tables is a mixture of fixed sets, so the fixed statement gives the random one by averaging; a fixed W is independent
--   - encoding: the parameters (9): U, q_fin, P_fin → totalBuckets β s ε, finCount β s ε, 2^(finBits s ε lim), with ⌈u⌉₂ = 2^⌈log₂⌈u⌉⌉ and 0 < β ≤ 1/8 (U depends on β through C = 2^24/β); reason: same parameters
--   - encoding: q_fin independent uniform pairs → the uniform law on Fin q_fin → (matrix × shift); reason: same law
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 46 (PDF p. 49), Lemma D.5

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Locators
import Definitions.Def_SparseWalsh_Approx_Algorithm3

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma D.5** (Final coefficient estimates), p. 46 (PDF p. 49). Let `1 ≤ s ≤ 2^d`,
`0 < ε ≤ 1`, `0 < β ≤ 1/8`, `T` the support of an optimal `s`-term approximation of `f` and
`τ = (Σ_{a ∉ T} f̂(a)²)^{1/2}`. The final estimation list `E_fin` of Algorithm 3 has `q_fin`
independent uniform pairs `(C, y)`, `C ∈ F_2^{(log₂ P_fin)×d}`, with the parameters `U`, `q_fin`,
`P_fin` of (9). For every candidate set `W` with `|W| ≤ U` (fixed, hence independent of the final
tables), with probability at least `63/64` every `a ∈ W` satisfies
`|Est_{E_fin}(f̂, a) − f̂(a)| ≤ ρ_j`, `ρ_j = ετ/(16√s)` for `j = s` and `ρ_j = √ε τ/(4√s)` for
`j = 2s`; and when `τ = 0` all these estimates are exact on this event. -/
theorem lemma_D_5 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 8) {d s : ℕ} (hd : 1 ≤ d) (hs : 1 ≤ s)
    (hsd : s ≤ 2 ^ d) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (lim : OutLimit) (f : Cube d → ℝ)
    (T : Finset (Cube d)) (hT : IsOptimalSupport s f T) (W : Finset (Cube d))
    (hW : W.card ≤ totalBuckets β s ε) :
    let τ : ℝ := Real.sqrt (tailSq f T)
    let ρj : ℝ := match lim with
      | .single => ε * τ / (16 * Real.sqrt s)
      | .double => Real.sqrt ε * τ / (4 * Real.sqrt s)
    let law := PMF.uniformOfFintype
      (Fin (finCount β s ε) → Matrix (Fin (finBits s ε lim)) (Fin d) (ZMod 2) × Cube d)
    let good := {E : Fin (finCount β s ε) → Matrix (Fin (finBits s ε lim)) (Fin d) (ZMod 2) ×
      Cube d | ∀ a ∈ W, |est E (hat f) a - hat f a| ≤ ρj}
    (63 / 64 : ENNReal) ≤ law.toOuterMeasure good ∧
    (tailSq f T = 0 → ∀ E ∈ good, ∀ a ∈ W, est E (hat f) a = hat f a) := by sorry

end SparseWalsh.Approx
