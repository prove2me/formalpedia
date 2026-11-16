-- Prove2me | Theorems.Thm_PlantedSubgraphLD_Supplement_theorem_A_3
-- name    : PlantedSubgraphLD.Supplement.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:59:47.306949+00:00
-- url     : https://prove2.me/theorems/3218b010-4cef-45bf-b95f-b57e1bdeb862
-- title:
--   Theorem A.3 — a low-degree–statistical gap for bounded-degree, high-girth planted graphs above criticality
-- statement:
--   Fix constants $r\in(0,1/2)$, $\gamma\in(0,1)$, an even integer $D\ge6$, and $A>0$, $\kappa>0$. Set $m_n=\lfloor n^r\rfloor$ and $D_n=\lceil(\log n)^2\rceil$. Then there is a constant $c_0>1$, depending only on $(r,\gamma,D,A,\kappa)$, with the following property.
--
--   Let $\varepsilon\in(0,1)$ satisfy (A.1), $(1-\varepsilon)D/2>1$. Let $(\Gamma_n)$ be a sequence of simple graphs on $[m_n]$ such that, for all sufficiently large $n$,
--
--   1. (A.2) $\max_{v\in[m_n]}\deg_{\Gamma_n}(v)\le D$;
--   2. (A.3) $e(\Gamma_n[U])\le\bigl(1+\frac{A}{\log n}\bigr)|U|$ for every $U\subseteq[m_n]$ with $2\le|U|\le m_n^{\gamma}$;
--   3. (A.4) $\mathrm{girth}(\Gamma_n)\ge\kappa\log n$;
--
--   and (A.5) $e(\Gamma_n)/m_n\to D/2$. Let $Q_n=G(n,c/n)$, let $P^{\mathrm{reg}}_n$ plant a uniformly random copy of $\Gamma_n$ in an independent sample of $Q_n$, $L^{\mathrm{reg}}_n=dP^{\mathrm{reg}}_n/dQ_n$, and let $T_\varepsilon$ be the noise operator. Then for every fixed $c\ge c_0$,
--
--   $$
--   \bigl\|(L^{\mathrm{reg}}_n)^{\le D_n}\bigr\|^2_{L^2(Q_n)}\longrightarrow1 \quad\text{(A.6)}\qquad\text{and}\qquad \bigl\|T_\varepsilon P^{\mathrm{reg}}_n-Q_n\bigr\|_{\mathrm{TV}}\longrightarrow1 \quad\text{(A.7)}.
--   $$
--
--   Lemma A.1 of the paper constructs such a sequence with $A=A(D,r,\gamma)$ and $\kappa=\kappa(D,r)$, so the planted model has a vanishing degree-$(\log n)^2$ advantage and yet stays statistically distinguishable from the null after noise. This shows (Remark 1.3) that above criticality some structural restriction on the planted graph, such as the treewidth condition of Theorem 1.1, is necessary.
--
--   **Formalization Note** $e(\Gamma_n[U])$ counts the pairs $u<v$ in $U$ adjacent in $\Gamma_n$; "girth $\ge\kappa\log n$" says every cycle has length at least $\kappa\log n$, so a forest qualifies. Logarithms are natural. The bounded degree $D$ is named `Δ` in Lean, to keep it apart from the low-degree level $D_n$. The laws, the low-degree norm and total variation are the mission's published definitions.
--
--   Differences from the source:
--   - generalization: the sequence from Lemma A.1, with A = A(D, r, γ), κ = κ(D, r), and c0 = c0(D, r, γ) → every sequence satisfying (A.2)–(A.5) for arbitrary A, κ > 0, with c0 depending on (r, γ, D, A, κ); reason: the proof of Theorem A.3 (pp.30–32) uses only (A.2)–(A.5); applied to the sequence of Lemma A.1 it gives the printed statement with c0(D, r, γ)
--   - generalization: (A.2)–(A.4) for every n → (A.2)–(A.4) for all sufficiently large n; reason: a weaker hypothesis; every sequence satisfying them for every n satisfies them eventually, and the conclusions are limits
--   - encoding: ε fixed first, D chosen with (A.1), c0 = c0(D, r, γ) → c0 chosen before ε, for every ε ∈ (0, 1) with (1 − ε)D/2 > 1; reason: the printed dependence c0(D, r, γ) excludes ε, so the constant is uniform in ε (its choice on p.31 involves only D, A, r, κ)
--   - encoding: mn = ⌊n^r⌋, Dn = ⌈(log n)²⌉, e(Γn[U]), girth(Γn) ≥ κ log n, D/2 − o(1), 1 + o(1), 1 − o(1) → m with m n = ⌊n^r⌋₊, ⌈(log n)^2⌉₊, the number of adjacent pairs u < v in U, every cycle walk has length ≥ κ log n, Tendsto to Δ/2, Tendsto to 1; reason: Lean notation for the same quantities
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Appendix A, setup (A.1), p.28 (PDF p.30); Lemma A.1 (A.2)–(A.5) and Theorem A.3 (A.6)–(A.7), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_noisedPlanted
import Definitions.Def_PlantedSubgraphLD_lowDegNormSq
import Definitions.Def_PlantedSubgraphLD_tvDist

open Filter Classical

namespace PlantedSubgraphLD.Supplement

open PlantedSubgraphLD

/-- **Theorem A.3 (low-degree–statistical gap above criticality).** Chen, Li, *Rigorous Low-Degree
Implications for Planted Subgraph Detection: Noise and Treewidth* (manuscript of Nov. 3, 2026,
arXiv:2608.06279, sha256 405d09c0…), Appendix A, pp.28–29 (PDF pp.30–31).

Setup, p.28: "Fix constants r ∈ (0, 1/2), γ ∈ (0, 1), ε ∈ (0, 1), and choose an even integer
D ≥ 6 such that (1 − ε)D/2 > 1. (A.1) Set mn := ⌊n^r⌋, Dn := ⌈(log n)²⌉." Lemma A.1, p.29: a
sequence of simple graphs Γn on [mn] and constants A, κ > 0 with "max_v degΓn(v) ≤ D (A.2),
e(Γn[U]) ≤ (1 + A/log n)|U| for every U ⊆ [mn] with 2 ≤ |U| ≤ mn^γ (A.3), girth(Γn) ≥ κ log n
(A.4), e(Γn)/mn = D/2 − o(1) (A.5)". P^reg_n plants a uniformly random copy of Γn in an
independent sample from Qn = G(n, c/n). Theorem A.3, p.29: "There exists a constant
c0 = c0(D, r, γ) > 1 such that, for every fixed c ≥ c0, ‖(L^reg_n)^{≤Dn}‖²_{L²(Qn)} = 1 + o(1).
(A.6) Nevertheless, ‖TεP^reg_n − Qn‖TV = 1 − o(1). (A.7)"

**Formalization Note** The theorem is stated for every sequence satisfying (A.2)–(A.5) with given
`A, κ > 0` (the hypotheses the proof uses), and `c₀` depends only on `(r, γ, D, A, κ)`: it is chosen
before `ε`, the sequence and `c`. Lemma A.1 provides such a sequence with `A = A(D, r, γ)`,
`κ = κ(D, r)`, which gives the printed `c₀(D, r, γ)`. Conditions (A.2)–(A.4) are assumed for all
large `n` (`∀ᶠ n in atTop`). `e(Γₙ[U])` counts the pairs `u < v` in `U` adjacent in `Γₙ`; girth
`≥ κ log n` says every cycle has length `≥ κ log n` (vacuous for a forest, girth `∞`). Logarithms
are natural (§3.1). `m n = ⌊n^r⌋₊`, `Dₙ = ⌈(log n)²⌉₊`. The bounded degree `D` of the page is the
variable `Δ` here, to keep it apart from the low-degree level `Dₙ`. -/
theorem theorem_A_3 (r γ : ℝ) (hr0 : 0 < r) (hr1 : r < 1 / 2) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Δ : ℕ) (hΔ6 : 6 ≤ Δ) (hΔeven : Even Δ) (A κ : ℝ) (hA : 0 < A) (hκ : 0 < κ) :
    ∃ c₀ : ℝ, 1 < c₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → 1 < (1 - ε) * (Δ : ℝ) / 2 →
      ∀ (m : ℕ → ℕ), (∀ n, m n = ⌊(n : ℝ) ^ r⌋₊) →
      ∀ (Γ : ∀ n, SimpleGraph (Fin (m n))),
        -- (A.2) maximum degree at most Δ
        (∀ᶠ n in atTop, ∀ v : Fin (m n), (Γ n).degree v ≤ Δ) →
        -- (A.3) local sparsity
        (∀ᶠ n in atTop, ∀ U : Finset (Fin (m n)), 2 ≤ U.card → (U.card : ℝ) ≤ (m n : ℝ) ^ γ →
          ((((U ×ˢ U).filter (fun p => p.1 < p.2 ∧ (Γ n).Adj p.1 p.2)).card : ℕ) : ℝ) ≤
            (1 + A / Real.log (n : ℝ)) * U.card) →
        -- (A.4) girth at least κ log n
        (∀ᶠ n in atTop, ∀ (v : Fin (m n)) (p : (Γ n).Walk v v), p.IsCycle →
          κ * Real.log (n : ℝ) ≤ p.length) →
        -- (A.5) e(Γₙ)/mₙ → Δ/2
        Tendsto (fun n => ((Γ n).edgeFinset.card : ℝ) / (m n : ℝ)) atTop
          (nhds ((Δ : ℝ) / 2)) →
        ∀ c : ℝ, c₀ ≤ c →
          -- (A.6)
          Tendsto (fun n => lowDegNormSq c n (Γ n) ⌈(Real.log (n : ℝ)) ^ 2⌉₊) atTop (nhds 1) ∧
          -- (A.7)
          Tendsto (fun n => tvDist (noisedPlanted c ε n (Γ n)) (erdosRenyi c n)) atTop
            (nhds 1) := by sorry

end PlantedSubgraphLD.Supplement
