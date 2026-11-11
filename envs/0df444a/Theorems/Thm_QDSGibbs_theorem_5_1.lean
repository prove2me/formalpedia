-- Prove2me | Theorems.Thm_QDSGibbs_theorem_5_1
-- name    : QDSGibbs.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:08.623967+00:00
-- url     : https://prove2.me/theorems/3412daf1-f6e8-4e23-9042-c77b6fef9d37
-- title:
--   Theorem 5.1 — all-temperature rapid mixing of QBP block Gibbs samplers on quantum spin chains
-- statement:
--   Consider a quantum spin chain $\Lambda=[N]$ with local dimensions $2\le d_i\le d$ and nearest-neighbour Hamiltonian $H=\sum_{i=1}^NV_i+\sum_{i=1}^{N-1}W_i$, with Hermitian on-site terms $V_i$ of arbitrary norm and Hermitian bond terms $W_i$ on $\{i,i+1\}$; let $J_{\mathrm{int}}$ be its interaction strength (2.2). For $\ell\ge2$ and $T>0$ let $\Phi_B=e^{T\mathcal K_B}$ be the QBP block updates over the labelled blocks $\mathcal W_\ell$, and
--
--   $$
--   \mathcal L=\frac1\ell\sum_{B\in\mathcal W_\ell}(\Phi_B-\mathrm{id}).
--   $$
--
--   **Theorem.** For every $\beta>0$ there are a block length $\ell\ge2$ and an evolution time $T>0$, depending only on $\beta$, $J_{\mathrm{int}}$ and $d$, with
--
--   $$
--   \ell\le C_d(1+\beta J_{\mathrm{int}})^8e^{8\beta J_{\mathrm{int}}},\qquad T\le C_de^{2\beta J_{\mathrm{int}}}\log(2+\beta J_{\mathrm{int}}),
--   $$
--
--   such that the channels $(\Phi_B)_{B\in\mathcal W_\ell}$, which all fix $\sigma_{\beta,H}=e^{-\beta H}/\mathrm{Tr}\,e^{-\beta H}$, satisfy the quantum Dobrushin–Shlosman condition (4.14) with $\kappa=1/2$. Then $\sigma_{\beta,H}$ is the unique stationary state of $\mathcal L$, and for every state $\rho$ and $t\ge0$,
--
--   $$
--   \|e^{t\mathcal L}(\rho)-\sigma_{\beta,H}\|_1\le2Ne^{-t/2}.
--   $$
--
--   The constant $C_d$ depends only on $d$; the parameters $\ell,T$ are uniform in the chain length and in the on-site fields. The sampler therefore mixes in time $O(\log(N/\varepsilon))$ at every fixed finite temperature.
--
--   **Formalization Note** The DS condition is written as (5.30) in $[0,\infty]$: $\sum_BD_B(j)+\ell/2\le N+\ell-1$ for every site $j$.
--
--   Differences from the source:
--   - reading: $\ell, T$ "depending only on $\beta, J_{\mathrm{int}}, d$"; $C_d$ "depending only on $d$" → $\forall d\,\exists C_d>0\,\forall\beta>0\,\forall J\ge0\,\exists\ell\ge2\,\exists T>0$, then for every $N\ge1$, every local dimensions $2\le d_i\le d$ and every chain with $J_{\mathrm{int}}(H)=J$; reason: the literal reading of the dependence; $\ell, T$ uniform in $N$ and the on-site fields, as Proposition 5.11 states
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: the labelled family $\mathcal W_\ell=(B_a)_{a=2-\ell}^N$ → labels $k\in\{0,\dots,N+\ell-2\}$ with block $\{i:k+1\le i+\ell,\ i\le k\}$ (`block N ℓ k`); reason: label $k$ is the paper's $a=k+2-\ell$; coinciding intervals keep distinct labels
--   - encoding: (5.30): $\sum_{B\in\mathcal W_\ell}[D_B(j)-1]\le-\ell/2$ → $\sum_BD_B(j)+\ell/2\le N+\ell-1$ in $[0,\infty]$; reason: $N+\ell-1$ is the number of labels; equivalent when every $D_B(j)$ is finite, and false (not vacuous) otherwise
--   - encoding: "$\sigma_{\beta,H}$ is the unique stationary state of $\mathcal L$" → $\mathcal L(\sigma_{\beta,H})=0$ and every state $\rho$ with $\mathcal L(\rho)=0$ equals $\sigma_{\beta,H}$; reason: stationarity of $e^{t\mathcal L}$ is $\mathcal L\rho=0$
--   - encoding: Definition 4.3: a family of channels with common fixed state → each $\Phi_B$ is a channel (Kraus form) with $\Phi_B(\sigma_{\beta,H})=\sigma_{\beta,H}$; reason: the requirement of Definition 4.3 that (4.14) refers to
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Theorem 5.1, p.39; (5.2)–(5.4), p.39; (5.30), p.51

import Mathlib
import Definitions.Def_QDSGibbs_chainGen
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ENNReal

namespace QDSGibbs

/-- **Theorem 5.1 (All-temperature chain mixing)** (Rouzé–Stilck França, *Rapid mixing of Gibbs
samplers via quantum Dobrushin–Shlosman conditions*, arXiv:2610.03578, held file sha256 ede55815…,
Theorem 5.1, p.39). For every `β > 0` there are a block length `ℓ ≥ 2` and an evolution time `T > 0`,
depending only on `β, J_int, d`, such that the QBP block channels `(Φ_B)_{B ∈ W_ℓ}` satisfy the
quantum DS condition (4.14) with `κ = 1/2`, with `ℓ ≤ C_d (1+βJ_int)^8 e^{8βJ_int}` and
`T ≤ C_d e^{2βJ_int} log(2+βJ_int)` (5.3); then `σ_{β,H}` is the unique stationary state of `L` and
`‖e^{tL}(ρ) − σ_{β,H}‖₁ ≤ 2N e^{−t/2}` for every state `ρ` and `t ≥ 0` (5.4).

**Formalization Note**
* Quantifier order: `C` (= `C_d`) depends only on the local dimension bound `dmax` (= `d`); `ℓ, T`
  depend only on `dmax, β, J`; then the claim holds for every chain length `N`, every local dimension
  vector with `2 ≤ d_i ≤ dmax`, every Hermitian on-site term `V_i` (any norm) and every Hermitian bond
  `W_i` with `J_int(H) = J` ((2.2): `J_int` excludes the on-site terms).
* The DS clause is (5.30), `Σ_{B ∈ W_ℓ} [D_B(j) − 1] ≤ −ℓ/2`, written in `ℝ≥0∞` as
  `Σ_B D_B(j) + ℓ/2 ≤ N + ℓ − 1` (`N + ℓ − 1` is the number of labels); Definition 4.3 also requires
  a family of channels with a common fixed state, here `σ_{β,H}`.
* Blocks are labelled by `Fin (N + ℓ − 1)` (`block`), `L = chainGen`, `e^{tL} = sexp`. -/
theorem theorem_5_1 :
    ∀ dmax : ℕ, 2 ≤ dmax → ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → ∀ J : ℝ, 0 ≤ J →
      ∃ ℓ : ℕ, 2 ≤ ℓ ∧ ∃ T : ℝ, 0 < T ∧
        (ℓ : ℝ) ≤ C * (1 + β * J) ^ 8 * Real.exp (8 * β * J) ∧
        T ≤ C * Real.exp (2 * β * J) * Real.log (2 + β * J) ∧
        ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i ∧ d i ≤ dmax) →
          ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W →
            jint (chain V W) = J →
            (∀ k : Fin (N + ℓ - 1),
                IsChannel (blockChannel β (chain V W) (block N ℓ k) Finset.univ T) ∧
                blockChannel β (chain V W) (block N ℓ k) Finset.univ T (gibbs β (ham (chain V W))) =
                  gibbs β (ham (chain V W))) ∧
            (∀ j : Fin N,
                ∑ k : Fin (N + ℓ - 1),
                    influence (blockChannel β (chain V W) (block N ℓ k) Finset.univ T) j +
                  (ℓ : ℝ≥0∞) / 2 ≤ ((N + ℓ - 1 : ℕ) : ℝ≥0∞)) ∧
            chainGen β V W ℓ T (gibbs β (ham (chain V W))) = 0 ∧
            (∀ ρ : Op d, IsState ρ → chainGen β V W ℓ T ρ = 0 → ρ = gibbs β (ham (chain V W))) ∧
            (∀ ρ : Op d, IsState ρ → ∀ t : ℝ, 0 ≤ t →
              traceNorm (sexp (chainGen β V W ℓ T) t ρ - gibbs β (ham (chain V W))) ≤
                2 * (N : ℝ) * Real.exp (-t / 2)) := by sorry

end QDSGibbs
