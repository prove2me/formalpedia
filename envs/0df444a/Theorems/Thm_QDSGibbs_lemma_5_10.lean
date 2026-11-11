-- Prove2me | Theorems.Thm_QDSGibbs_lemma_5_10
-- name    : QDSGibbs.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:32.297576+00:00
-- url     : https://prove2.me/theorems/e1a23981-ae80-4a1f-9a3f-2f67ca80efb5
-- title:
--   Lemma 5.10 — uniform localized influences
-- statement:
--   On a nearest-neighbour chain with local dimensions $2\le d_i\le d$ and $\beta>0$, let $M=e^{\beta J_{\mathrm{int}}/2}$ and suppose the block Gibbs state $\sigma^B_\beta$ of an interval $B$ satisfies (5.18) with $C_{\mathrm{cl}}\ge0$ and a nonnegative nonincreasing profile $f$. Set
--
--   $$
--   A_u=8(u+1)+4\sum_{v=0}^\infty\min\{1,\,3M^8C_{\mathrm{cl}}d^{4(u+1)}f(v)\}.
--   $$
--
--   For every $T\ge0$, integer $u\ge0$ and site $j$, the influence $D_{B,u}(j)$ of $\Phi_{B,u}(T)$ satisfies
--
--   $$
--   D_{B,u}(j)\le\begin{cases}e^{-M^{-4}T},& j\in I_u(B),\\ A_u+4|B|e^{-M^{-4}T},& j\in C_u(B),\\ 1,& j\notin B^{\le u+1}.\end{cases}
--   $$
--
--   For the profile of (5.18), $f(v)=e^{-c_{\mathrm{cl}}\sqrt v}$ with $c_{\mathrm{cl}}\ge ce^{-4\beta J_{\mathrm{int}}}/(1+\beta J_{\mathrm{int}})$, also
--
--   $$
--   A_u\le C_d\big[(u+1)+(1+\beta J_{\mathrm{int}})^2e^{8\beta J_{\mathrm{int}}}(u+\beta J_{\mathrm{int}}+1)^2\big].
--   $$
--
--   The boundary influence is bounded independently of the block length, apart from a term decaying exponentially in $T$; this is what lets interior contraction dominate for long blocks.
--
--   **Formalization Note** In the second part $C_d$ depends on $d$ and on the numerical constants $C_{\mathrm{cl}}$, $c$ of (5.18), and the bound is stated for all $\beta>0$, $J_{\mathrm{int}}\ge0$.
--
--   Differences from the source:
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
--   - reading: the profile $f$ and constant $C_{\mathrm{cl}}$ of (5.18) → $f$ nonnegative and nonincreasing, $C_{\mathrm{cl}}\ge0$; reason: as in Lemma 5.9
--   - generalization: (5.21) for the specific profile and constant of (5.18) → (5.21) for every $C_{\mathrm{cl}}\ge0$ and nonnegative nonincreasing $f$ for which $\sigma^B_\beta$ satisfies (5.18); reason: the proof uses only (5.18) through Lemma 5.9; the paper's profile is one such $f$
--   - generalization: (5.22) at $J_{\mathrm{int}}$ of the chain → (5.22) for every $\beta>0$ and every $J\ge0$, with $C_d$ depending on $d$ and the numerical constants $C_{\mathrm{cl}}, c$ of (5.18); reason: (5.22) is a numerical inequality; every chain's $J_{\mathrm{int}}$ is a $J\ge0$
--   - encoding: $A_u$ as a real series → $A_u$ in $[0,\infty]$; reason: the series has nonnegative terms; a divergent series gives $\infty$, making the bound harder, not vacuous
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 5.10, pp.46–47; (5.18), p.45

import Mathlib
import Definitions.Def_QDSGibbs_ClusterBound
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ENNReal

namespace QDSGibbs

/-- **Lemma 5.10 (Uniform localized influences)** (arXiv:2610.03578, held file sha256 ede55815…,
Lemma 5.10, pp.46–47). With `M` from Lemma 5.4, set
`A_u := 8(u + 1) + 4 Σ_{v=0}^∞ min{1, 3M^8 C_cl d^{4(u+1)} f(v)}` (5.20). For every `T ≥ 0`, interval
`B ⊆ [N]`, integer `u ≥ 0` and site `j`,
`D_{B,u}(j) ≤ e^{−M^{−4}T}` (`j ∈ I_u(B)`), `≤ A_u + 4|B|e^{−M^{−4}T}` (`j ∈ C_u(B)`),
`≤ 1` (`j ∉ B^{≤u+1}`) (5.21). For the profile in (5.18), also
`A_u ≤ C_d[(u + 1) + (1 + βJ_int)^2 e^{8βJ_int}(u + βJ_int + 1)^2]` (5.22).

**Formalization Note**
* (5.21): §5 chain (`2 ≤ d_i ≤ dmax`, `dmax` the paper's `d`), `β > 0`, `M = e^{βJ_int/2}`; `C_cl ≥ 0`
  and the nonnegative nonincreasing profile `f` are any for which `σ^B_β` satisfies (5.18)
  (`ClusterBound`, the hypothesis Lemma 5.9 uses). `D_{B,u}(j)` is the influence of
  `Φ_{B,u}(T) = blockChannel β I B (C_u(B)) T`; `A_u = aU` is `ℝ≥0∞`-valued.
* (5.22): the profile `f(v) = e^{−c_cl √v}` with `c_cl ≥ c e^{−4βJ_int}/(1+βJ_int)`, `c > 0` the constant
  of (5.18) and `C_cl` the numerical constant there; `C_d` depends only on `d` (and these numerical
  constants), and the bound holds for every `β > 0`, `J_int ≥ 0`. -/
theorem lemma_5_10 :
    (∀ (N : ℕ), 1 ≤ N → ∀ (dmax : ℕ) (d : Fin N → ℕ), (∀ i, 2 ≤ d i ∧ d i ≤ dmax) →
      ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
        ∀ Ccl : ℝ, 0 ≤ Ccl → ∀ f : ℝ → ℝ, Antitone f → (∀ v, 0 ≤ f v) →
          ∀ B : Finset (Fin N), IsInterval B →
            ClusterBound (gibbs β (hamOn (chain V W) B)) B Ccl f →
            ∀ T : ℝ, 0 ≤ T → ∀ u : ℕ, ∀ j : Fin N,
              (j ∈ interiorU B u →
                influence (blockChannel β (chain V W) B (bdryNbhd B u) T) j ≤
                  ENNReal.ofReal (Real.exp (-((Real.exp (β * jint (chain V W) / 2) ^ 4)⁻¹ * T)))) ∧
              (j ∈ bdryNbhd B u →
                influence (blockChannel β (chain V W) B (bdryNbhd B u) T) j ≤
                  aU (Real.exp (β * jint (chain V W) / 2)) Ccl dmax f u +
                    ENNReal.ofReal (4 * B.card *
                      Real.exp (-((Real.exp (β * jint (chain V W) / 2) ^ 4)⁻¹ * T)))) ∧
              (j ∉ nbhd B ((u : ℝ) + 1) →
                influence (blockChannel β (chain V W) B (bdryNbhd B u) T) j ≤ 1)) ∧
    (∀ Ccl c : ℝ, 0 ≤ Ccl → 0 < c → ∀ dmax : ℕ, 2 ≤ dmax → ∃ Cd : ℝ, 0 < Cd ∧
      ∀ β J : ℝ, 0 < β → 0 ≤ J → ∀ ccl : ℝ, c * Real.exp (-(4 * β * J)) / (1 + β * J) ≤ ccl →
        ∀ u : ℕ,
          aU (Real.exp (β * J / 2)) Ccl dmax (fun v => Real.exp (-(ccl * Real.sqrt v))) u ≤
            ENNReal.ofReal (Cd * (((u : ℝ) + 1) +
              (1 + β * J) ^ 2 * Real.exp (8 * β * J) * ((u : ℝ) + β * J + 1) ^ 2))) := by sorry

end QDSGibbs
