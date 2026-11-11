-- Prove2me | Theorems.Thm_QDSGibbs_proposition_5_11
-- name    : QDSGibbs.proposition_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:39.330063+00:00
-- url     : https://prove2.me/theorems/e38dab3c-a814-4d41-826c-a263e0ab7a87
-- title:
--   Proposition 5.11 — quantum DS with $\kappa=1/2$ for the smoothed heat-bath block updates
-- statement:
--   For every local dimension bound $d$, inverse temperature $\beta>0$ and interaction strength $J_{\mathrm{int}}\ge0$, there are an integer $\ell\ge2$ and a time $T>0$, depending only on these parameters, such that for every nearest-neighbour chain with local dimensions $2\le d_i\le d$, arbitrary on-site terms and interaction strength $J_{\mathrm{int}}$, the block updates $(\Phi_B(T))_{B\in\mathcal W_\ell}$ satisfy
--
--   $$
--   \sum_{B\in\mathcal W_\ell}[D_B(j)-1]\le-\frac\ell2,\qquad j\in[N],
--   $$
--
--   and
--
--   $$
--   \ell\le C_d(1+\beta J_{\mathrm{int}})^8e^{8\beta J_{\mathrm{int}}},\qquad T\le C_de^{2\beta J_{\mathrm{int}}}\log(2+\beta J_{\mathrm{int}}),
--   $$
--
--   with $C_d$ depending only on $d$. In particular the same $\ell,T$ work for every chain length $N$ and every choice of the on-site terms.
--
--   Differences from the source:
--   - reading: $\ell, T$ "depending only on $\beta, J_{\mathrm{int}}, d$"; $C_d$ "depending only on $d$" → $\forall d\,\exists C_d>0\,\forall\beta>0\,\forall J\ge0\,\exists\ell\ge2\,\exists T>0$, then for every $N\ge1$, every local dimensions $2\le d_i\le d$ and every chain with $J_{\mathrm{int}}(H)=J$; reason: the literal reading of the dependence; $\ell, T$ uniform in $N$ and the on-site fields, as Proposition 5.11 states
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: the labelled family $\mathcal W_\ell=(B_a)_{a=2-\ell}^N$ → labels $k\in\{0,\dots,N+\ell-2\}$ with block $\{i:k+1\le i+\ell,\ i\le k\}$ (`block N ℓ k`); reason: label $k$ is the paper's $a=k+2-\ell$; coinciding intervals keep distinct labels
--   - encoding: (5.30): $\sum_{B\in\mathcal W_\ell}[D_B(j)-1]\le-\ell/2$ → $\sum_BD_B(j)+\ell/2\le N+\ell-1$ in $[0,\infty]$; reason: $N+\ell-1$ is the number of labels; equivalent when every $D_B(j)$ is finite, and false (not vacuous) otherwise
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Proposition 5.11, p.51

import Mathlib
import Definitions.Def_QDSGibbs_chainGen
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ENNReal

namespace QDSGibbs

/-- **Proposition 5.11 (Quantum DS for the smoothed heat-bath block updates)** (arXiv:2610.03578,
held file sha256 ede55815…, Proposition 5.11, p.51). For every fixed `β, J_int, d` there are an
integer `ℓ ≥ 2` and a time `T > 0`, depending only on these parameters, such that the family
`(Φ_B(T))_{B ∈ W_ℓ}` satisfies `Σ_{B ∈ W_ℓ} [D_B(j) − 1] ≤ −ℓ/2` for every `j ∈ [N]` (5.30); the
parameters satisfy (5.3); the same `ℓ, T` work for every chain length `N` and every choice of the
on-site terms `V_i`.

**Formalization Note** Quantifier order as in Theorem 5.1: `C_d` before `β, J`; `ℓ, T` before `N`,
the local dimensions (`2 ≤ d_i ≤ dmax`) and the chain terms with `J_int(H) = J`. (5.30) is written in
`ℝ≥0∞` as `Σ_B D_B(j) + ℓ/2 ≤ N + ℓ − 1`, the number of labels being `N + ℓ − 1`. -/
theorem proposition_5_11 :
    ∀ dmax : ℕ, 2 ≤ dmax → ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → ∀ J : ℝ, 0 ≤ J →
      ∃ ℓ : ℕ, 2 ≤ ℓ ∧ ∃ T : ℝ, 0 < T ∧
        (ℓ : ℝ) ≤ C * (1 + β * J) ^ 8 * Real.exp (8 * β * J) ∧
        T ≤ C * Real.exp (2 * β * J) * Real.log (2 + β * J) ∧
        ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i ∧ d i ≤ dmax) →
          ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W →
            jint (chain V W) = J →
            ∀ j : Fin N,
              ∑ k : Fin (N + ℓ - 1),
                  influence (blockChannel β (chain V W) (block N ℓ k) Finset.univ T) j +
                (ℓ : ℝ≥0∞) / 2 ≤ ((N + ℓ - 1 : ℕ) : ℝ≥0∞) := by sorry

end QDSGibbs
