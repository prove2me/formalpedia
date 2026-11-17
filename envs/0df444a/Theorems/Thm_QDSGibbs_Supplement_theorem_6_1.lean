-- Prove2me | Theorems.Thm_QDSGibbs_Supplement_theorem_6_1
-- name    : QDSGibbs.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:29:07.665991+00:00
-- url     : https://prove2.me/theorems/91b63aed-bca5-44ea-a200-5722aed7e936
-- title:
--   Theorem 6.1 — stability of the quantum DS condition: $\delta\le c/\beta$ keeps DS with $\kappa_0/2$
-- statement:
--   Fix $\beta>0$, a volume-independent upper bound $T>0$ and $\kappa_0>0$, together with the geometric data (local dimension bound $d$, polynomial volume growth constants $C_{\mathrm{vol}}\ge1$, $D\ge1$, the bounds $k$, $r\ge1$, $\nu$ of (2.1)), the reference intersite bound $J^{(0)}_{\mathrm{int}}$, and the block data (size bound $b$, a diameter bound, and the constants $V$, $\Xi$ of (6.2)). Then there is $c\in(0,1]$, depending only on these data, with the following property.
--
--   Let $H^{(0)}$ be a reference Hamiltonian with $J_{\mathrm{int}}(H^{(0)})\le J^{(0)}_{\mathrm{int}}$ and on-site terms of arbitrary norm, $Q=\sum_XQ_X$ a perturbation, $H=H^{(0)}+Q$, and $\delta=\sup_i\sum_{X\ni i}\|Q_X\|$ (6.1). Let $(B)$ be labelled blocks with rates $a_B>0$, neighbourhoods $R_B$ containing $B$ and every support crossing $B$ with
--   $$|R_B^{\le\rho}|\le V(1+\rho)^D,\qquad\sup_j\sum_{B:\,j\in R_B^{\le\rho}}a_B\le\Xi(1+\rho)^D\qquad(\rho\ge0),\qquad(6.2)$$
--   and block times $0<T_B\le T$. If the QBP channels $\Phi_B(H^{(0)})=e^{T_B\mathcal K_B(H^{(0)})}$ satisfy
--   $$\min_j\sum_Ba_B\bigl[1-D_{\Phi_B(H^{(0)})}(j)\bigr]\ge\kappa_0\qquad(6.4)$$
--   and $\delta\le c/\beta$, then the QBP channels $\Phi_B(H)=e^{T_B\mathcal K_B(H)}$ satisfy the quantum DS condition with constant $\kappa_0/2$; in particular $c$ does not depend on the volume or on the reference on-site norms.
--
--   This is the perturbative stability result behind the transverse-field Ising application: a strict quantum DS certificate survives every sufficiently small local perturbation, with a threshold uniform in the system size.
--
--   **Formalization Note** $c$ is chosen after the fixed data and before the system. The site set is explicitly nonempty, as required for the minimum in (6.4). $H$ is one labelled interaction `perturb I0 Q`; the (2.1) bounds apply to its combined family. The DS condition is written as $\sum_Ba_BD_{\Phi_B}(j)+\kappa\le\sum_Ba_B$ in $[0,\infty]$ for every $j$, with the base influence (2.11); the conclusion also records that $\sigma_{\beta,H}$ is a state and that the $\Phi_B(H)$ are channels fixing it (Definition 4.3).
--
--   Differences from the source:
--   - generalization: dist the underlying graph distance (or ℓ∞ on a lattice) → any metric dist on the sites (IsMetric), real exponent D; reason: the proof uses only the metric axioms, the (2.1) diameter bounds and polynomial volume growth (the Lieb–Robinson bound of Theorem 2.3 holds on such metric spaces); graph and lattice distances are special cases
--   - reading: the supports of H^{(0)} and of Q obey the (2.1) geometry (k, r, ν) → the (2.1) bounds imposed on the combined labelled family of H = H^{(0)} + Q; reason: the source does not say whether ν counts H^{(0)} and Q jointly; separate bounds ν give the combined bound 2ν and c may depend on ν, so both readings give the same theorem
--   - encoding: min_j Σ_B a_B[1 − D_{Φ_B}(j)] ≥ κ (6.4) and its κ0/2 conclusion → Σ_B a_B D_{Φ_B}(j) + κ ≤ Σ_B a_B in ℝ≥0∞ for every site j; reason: the same inequality; it fails when an influence is infinite
--   - encoding: the data on which c depends (geometric and intersite bounds, block parameters and rates, β, T, κ0) → explicit parameters dmax, D, C_vol, k, r, ν, J0, b, bdiam, V, Ξ, β, T, κ0 quantified before ∃ c; reason: this is the source's list of dependencies made explicit; w ≤ βbJ^{(0)}_int is controlled by these
--   - encoding: min_j in (6.4) is over the finite site set → hypothesis 1 ≤ N; reason: excludes only the empty system, where the minimum over sites is undefined
--   - encoding: hypothesis: the QBP channels of H^{(0)} satisfy the quantum DS condition (6.4) → the inequality (6.4) only, while the conclusion explicitly asserts that σ_{β,H} is a state and that the perturbed maps are channels fixing it; reason: the channel and common-fixed-state parts of Definition 4.3 hold for every QBP family (Proposition 3.4)
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Theorem 6.1, p.54 (setting (6.1) p.53, (6.2)–(6.3) p.54, (2.1) p.10, volume growth p.11)

import Mathlib
import Definitions.Def_QDSGibbs_Supplement_perturb
import Definitions.Def_QDSGibbs_blockChannel
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ENNReal

namespace QDSGibbs.Supplement

/-- **Theorem 6.1 (Stability of the quantum DS condition)** (Rouzé–Stilck França, *Rapid mixing of
Gibbs samplers via quantum Dobrushin–Shlosman conditions*, arXiv:2610.03578, held file sha256
ede55815…, Theorem 6.1, p.54). Fix `β > 0`, a volume-independent bound `T > 0` and `κ0 > 0`, the
geometric data (local dimension bound `d`, volume-growth constants `C_vol ≥ 1`, `D ≥ 1`, the (2.1)
bounds `k`, `r ≥ 1`, `ν`), the reference intersite bound `J^{(0)}_int`, and the block data (size `b`,
diameter, the constants `V`, `Ξ` of (6.2)). Then there is `c ∈ (0, 1]`, depending only on these data,
such that: for every system of any size, every reference `H^{(0)}` with `J_int(H^{(0)}) ≤ J^{(0)}_int`
and arbitrary on-site terms, every labelled block family with rates `a_B > 0`, neighbourhoods
`R_B` satisfying (6.2) and times `0 < T_B ≤ T`, and every perturbation `Q` with `δ ≤ c/β` (6.1): if the
QBP channels `Φ_B(H^{(0)}) = e^{T_B K_B(H^{(0)})}` satisfy the quantum DS condition (6.4) with rates
`a_B` and constant `κ0`, then the QBP channels `Φ_B(H) = e^{T_B K_B(H)}` of `H = H^{(0)} + Q` satisfy
the quantum DS condition with constant `κ0/2`.

**Formalization Note**
* Quantifier order: `c` comes after the fixed data and before the system (`N`, local dimensions,
  metric, Hamiltonians, blocks, rates, `R_B`, times), so it is independent of the volume, of the
  on-site norms of `H^{(0)}` and of the particular blocks.
* `1 ≤ N` makes explicit the nonempty site set implicit in the minimum over sites in (6.4).
* `H = H^{(0)} + Q` is one labelled interaction `perturb I0 Q`; the (2.1) bounds are imposed on this
  combined family, and `R_B` contains `B` and every support crossing `B` of either part. `δ` is
  `pertNorm Q` (single-site perturbations included).
* The DS condition `min_j Σ_B a_B [1 − D_{Φ_B}(j)] ≥ κ` is written, as in the base `theorem_4_4`, as
  `Σ_B a_B D_{Φ_B}(j) + κ ≤ Σ_B a_B` in `ℝ≥0∞` for every `j`, with the base `influence` (2.11); the
  conclusion also records that the `Φ_B(H)` are channels with the common fixed state `σ_{β,H}`
  (Definition 4.3). `Φ_B` is the base `blockChannel β · B univ T_B`.
* The distance is any metric on the sites (graph distance, or ℓ∞ on a lattice); `D` is real. -/
theorem theorem_6_1 :
    ∀ (dmax : ℕ) (D Cvol : ℝ) (k : ℕ) (r : ℝ) (ν : ℕ) (J0 : ℝ) (b : ℕ)
      (bdiam V Ξ β T κ0 : ℝ),
      2 ≤ dmax → 1 ≤ D → 1 ≤ Cvol → 1 ≤ r → 0 ≤ J0 → 0 < β → 0 < T → 0 < κ0 →
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
        ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i ∧ d i ≤ dmax) →
        ∀ (dist : Fin N → Fin N → ℝ), IsMetric dist → PolyGrowth dist Cvol D →
        ∀ (I0 Q : Interaction d), I0.IsValid → Q.IsValid →
          IsBoundedGeometry dist (perturb I0 Q) k r ν → jint I0 ≤ J0 →
        ∀ {ι : Type} [Fintype ι] (blk : ι → Finset (Fin N)) (a : ι → ℝ)
          (R : ι → Finset (Fin N)) (TB : ι → ℝ),
          (∀ B, (blk B).Nonempty ∧ (blk B).card ≤ b ∧
            ∀ i ∈ blk B, ∀ j ∈ blk B, dist i j ≤ bdiam) →
          (∀ B, 0 < a B) → (∀ B, 0 < TB B ∧ TB B ≤ T) →
          (∀ B, blk B ⊆ R B ∧
            ∀ α, Crosses ((perturb I0 Q).X α) (blk B) → (perturb I0 Q).X α ⊆ R B) →
          (∀ ρ : ℝ, 0 ≤ ρ →
            (∀ B, ((nbhdM dist (R B) ρ).card : ℝ) ≤ V * (1 + ρ) ^ D) ∧
            ∀ j : Fin N,
              ∑ B ∈ Finset.univ.filter (fun B => j ∈ nbhdM dist (R B) ρ), a B ≤ Ξ * (1 + ρ) ^ D) →
          pertNorm Q ≤ c / β →
          (∀ j : Fin N,
            ∑ B, ENNReal.ofReal (a B) * influence (blockChannel β I0 (blk B) Finset.univ (TB B)) j +
              ENNReal.ofReal κ0 ≤ ENNReal.ofReal (∑ B, a B)) →
          IsState (gibbs β (ham (perturb I0 Q))) ∧
          (∀ B, IsChannel (blockChannel β (perturb I0 Q) (blk B) Finset.univ (TB B)) ∧
            blockChannel β (perturb I0 Q) (blk B) Finset.univ (TB B)
                (gibbs β (ham (perturb I0 Q))) = gibbs β (ham (perturb I0 Q))) ∧
          ∀ j : Fin N,
            ∑ B, ENNReal.ofReal (a B) *
                influence (blockChannel β (perturb I0 Q) (blk B) Finset.univ (TB B)) j +
              ENNReal.ofReal (κ0 / 2) ≤ ENNReal.ofReal (∑ B, a B) := by sorry

end QDSGibbs.Supplement
