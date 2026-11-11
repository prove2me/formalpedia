-- Prove2me | Theorems.Thm_SumReLU_eq_M
-- name    : SumReLU.eq_M
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:00.180187+00:00
-- url     : https://prove2.me/theorems/f5b1a99c-21ef-4be0-905a-0f9dbe9f6b63
-- title:
--   Eq. (M) — $Z^{-1}\langle\hat\sigma_{2p+2}^{-1}\mathbb E[y\mathrm{He}_{2p+2}(x)],u^{\otimes p}\otimes\bar u^{\otimes p}\rangle=Z^{-1}\sum_i\beta_i|w_i\cdot u|^{2p}w_iw_i^\top$
-- statement:
--   Let $f(x)=\sum_{i=1}^k\beta_i\sigma(w_i\cdot x)$ with $\beta_i\in[0,1]$ and $\|w_i\|_2=1$, let $p\in\mathbb N$, $Z>0$ and $u\in\mathbb C^d$. With $x\sim N(0,I_d)$, $y=f(x)$ and $\mathrm{He}_{2p+2}$ the normalized Hermite tensor,
--   $$
--   \frac{1}{Z}\Big\langle\frac{1}{\hat\sigma_{2p+2}}\mathbb E\big[y\,\mathrm{He}_{2p+2}(x)\big],\ u^{\otimes p}\otimes\bar u^{\otimes p}\Big\rangle=\frac1Z\sum_{i=1}^k\beta_i\,|w_i\cdot u|^{2p}\,w_iw_i^\top ,
--   $$
--   where the contraction is over the first $2p$ indices and conjugates its first argument (which is real here). The identity holds entrywise for all $a,b\in[d]$.
--
--   It says that the filtered moment matrix, which can be estimated from samples, is a positive combination of the rank-one matrices $w_iw_i^\top$ weighted by $|w_i\cdot u|^{2p}$; a random probe $u$ then singles out one hidden vector.
--
--   Differences from the source:
--   - generalization: $Z=Z_p(\mathcal U)>0$ "a fixed parameter", $u$ drawn from $\mathcal U$, $p$ the filter degree → every $Z>0$, every $u\in\mathbb C^d$, every $p\in\mathbb N$; reason: the identity is pointwise in $u$ and linear in $Z^{-1}$, so it specializes to every choice of $\mathcal U$ and $p$
--   - encoding: a matrix identity → the identity entrywise, as complex numbers; reason: the contraction is complex-valued in general; both sides are real here
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Eq. (M), p.24 (PDF p.26); p.25 (PDF p.27); proof of Claim 4.15, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_reluHermite
import Definitions.Def_SumReLU_filterMatrix

namespace SumReLU

/-- **Eq. (M)**: the two forms of the filtered matrix agree.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Eq. (M), p.24 (PDF p.26): "M_{2p+2}(u) (i):= (1/Z_p(U)) ⟨(1/σ̂_{2p+2}) E_{(x,y)∼D}[y He_{2p+2}(x)],
u^{⊗p} ⊗ ū^{⊗p}⟩ (ii)= (1/Z_p(U)) ∑_{i=1}^k β_i |w_i · u|^{2p} w_i w_iᵀ, where Z_p(U) > 0 is a fixed
parameter depending on the sampling distribution U from which u is drawn and on the degree p";
derivation p.25 (PDF p.27) and proof of Claim 4.15, p.35 (PDF p.37).

**Formalization Note.** Entrywise for `a, b ∈ [d]`: the contraction is over the first `2p` indices
(§2, p.10), conjugating its first argument, which is real here. `Z` is any positive real (the page
fixes only `Z_p(U) > 0`) and `u` any vector of `ℂᵈ`; `p` any natural number. -/
theorem eq_M {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)) (hf : InClass β w)
    (p : ℕ) (Z : ℝ) (hZ : 0 < Z) (u : Fin d → ℂ) (a b : Fin d) :
    ((Z⁻¹ * (reluHermite (2 * p + 2))⁻¹ : ℝ) : ℂ) *
        contract (momentTensor β w (2 * p + 2)) (filter p u) a b =
      ((filterMatrix β w p Z u a b : ℝ) : ℂ) := by sorry

end SumReLU
