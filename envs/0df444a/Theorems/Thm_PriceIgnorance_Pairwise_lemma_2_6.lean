-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_lemma_2_6
-- name    : PriceIgnorance.Pairwise.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:13:05.576743+00:00
-- url     : https://prove2.me/theorems/31f1c478-296e-44fd-8151-833e5e80bb09
-- title:
--   Lemma 2.6 — the mod-$m$ masking gadget: $k$-wise independent, $X_n\sim\mu$, and $X_n$ determined by $X_1,\dots,X_{n-1}$
-- statement:
--   Fix integers $k\ge1$ and $m\ge2$, a distribution $\mu$ on $\mathbb Z_m$, and let $n=k+2$. Sample $X_n\sim\mu$ and, independently, $X_1,\dots,X_{n-2}$ i.i.d. uniform on $\mathbb Z_m$, and set
--   $$X_{n-1}=X_n-\sum_{i=1}^{n-2}X_i\pmod m .$$
--   Then:
--
--   1. $X_1,\dots,X_n$ are $k$-wise independent;
--   2. $X_n\sim\mu$;
--   3. $X_n$ is determined by $X_1,\dots,X_{n-1}$: there is a function $g$ with $X_n=g(X_1,\dots,X_{n-1})$.
--
--   With $k=2$ this is the gadget that hides each encoded sample in Theorem 3.16: any two of its variables are independent, yet the first three determine the fourth.
--
--   Differences from the source:
--   - encoding: random variables X_1..X_n on some probability space → the explicit space Z_m^k × Z_m with law Uni^{⊗k} ⊗ μ; 0-based indices (Lean index k = X_{n-1}, index k + 1 = X_n); reason: the construction fixes the joint law, so the canonical space loses nothing
--   - encoding: k-wise independence of Z_m-valued variables → KWiseIndep of their images under x ↦ (x.val : ℝ); reason: the embedding is injective, so independence is unchanged
--   - encoding: X_n is determined by X_1..X_{n-1} → ∃ g, X_n(ω) = g(X_1(ω),…,X_{n-1}(ω)) for every ω; reason: pointwise determination; the paper's identity X_n = Σ_{i<n} X_i holds everywhere
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 4, Lemma 2.6 (proof pp. 24–25)

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep
import Definitions.Def_PriceIgnorance_Pairwise_ModMask

open MeasureTheory

namespace PriceIgnorance.Pairwise

/-- Lemma 2.6 (p. 4): for `k ≥ 1`, `m ≥ 2` and a distribution `μ` on `ℤ_m`, with `n = k + 2`,
`X_n ∼ μ`, `X_1, …, X_{n-2}` i.i.d. uniform on `ℤ_m` independent of `X_n`, and
`X_{n-1} = X_n − Σ_{i ≤ n-2} X_i (mod m)`: the variables `X_1, …, X_n` are `k`-wise independent,
`X_n ∼ μ`, and `X_n` is determined by `X_1, …, X_{n-1}` (0-based indices in Lean). -/
theorem lemma_2_6 (k m : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) (μ : Measure (ZMod m))
    [IsProbabilityMeasure μ] :
    LaconicBarrier.KWiseIndep (maskLaw k m μ) (fun i ω => zr (maskVars k m i ω)) k ∧
    (maskLaw k m μ).map (maskVars k m (Fin.last (k + 1))) = μ ∧
    ∃ g : (Fin (k + 1) → ZMod m) → ZMod m,
      ∀ ω, maskVars k m (Fin.last (k + 1)) ω = g (fun i => maskVars k m (Fin.castSucc i) ω) := by sorry

end PriceIgnorance.Pairwise
