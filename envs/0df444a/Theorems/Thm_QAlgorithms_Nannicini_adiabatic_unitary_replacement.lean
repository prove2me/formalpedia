-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_adiabatic_unitary_replacement
-- name    : QAlgorithms.Nannicini.adiabatic_unitary_replacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:51:18.371144+00:00
-- url     : https://prove2.me/theorems/73c66b45-80f4-434d-bbf1-d7831a0a0e0c
-- title:
--   Replacing U_k ⋯ U_j by powers of U_1 in the discretized adiabatic evolution
-- statement:
--   Work in the setting of Theorem 9.17. Let $H(s)$, $s \in [0,1]$, be a time-dependent Hamiltonian on $\mathbb{C}^\iota$ with twice differentiable entries, entrywise derivatives $H'$, $H''$ and operator-norm bounds $\|H'(s)\| \le N_1$, $\|H''(s)\| \le N_2$ for all $s$. Let $|\varphi(s)\rangle$ be a unit vector with $H(s)|\varphi(s)\rangle = 0$ for every $s$, differentiable in $s$ with derivative $|\varphi'(s)\rangle$, and with its phase fixed by $\langle \varphi'(s)|\varphi(s)\rangle = 0$ (Eq. (9.20)). Let $\gamma > 0$ be a spectral gap around $0$: $0$ is a simple eigenvalue of every $H(s)$ and all other eigenvalues have absolute value at least $\gamma$. Let $\delta > 0$ and $T \ge \frac{10^3}{\delta^2}\max\{N_1^3/\gamma^4, N_1 N_2/\gamma^3\}$.
--
--   For a number $N$ of discretization steps put $U_j = e^{i\frac{T}{N} H(j/N)}$, $g_j = |\varphi(j/N)\rangle$, and let $p_1 = \mathrm{Proj}_{G_1^\perp}(g_0 - g_1)$ be the component of $g_0 - g_1$ orthogonal to $g_1$.
--
--   Then there are a constant $C$ and a threshold $N_0$, both independent of $N$ and $k$, such that for all $N \ge N_0$ and all $1 \le k \le N$
--
--   $$
--   \Bigl\| \sum_{j=1}^k U_k U_{k-1} \cdots U_j\, p_1 - \sum_{j=1}^k U_1^{k+1-j} p_1 \Bigr\| \le \frac{2(k+1)k\,N_1^2}{\gamma^2 N^2} + \frac{C k}{N^3}.
--   $$
--
--   The lemma bounds the error made in the proof of the adiabatic theorem when every unitary $U_j$ acting on the orthogonal component $p_1$ is replaced by $U_1$, which turns the evolution into a geometric sum that cancels.
--
--   **Formalization Note** This is a corrected statement. The source writes the remainder as $O(k/N^3)$ without saying how it depends on $k$. Following Rem. 9.14, the constant $C$ may depend on everything except $N$ (on $H$, $\varphi$, $T$, $\gamma$, $N_1$, $N_2$, $\delta$). It is quantified before $N$ and $k$, and the bound holds uniformly in $1 \le k \le N$. This is the reading the proof of Theorem 9.17 relies on when it applies the lemma at $k = M - 1 = O(N)$ with remainder $O(1/N^2)$. The evolution $\psi$ of Theorem 9.17 plays no role and is omitted.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 221, Lemma 9.20. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms.Stabilizer





/-- Corrected statement. Nannicini p.221, Lemma 9.20. Printed: "Let `p_j, U_j` for
`j = 1, …, N` be defined as in Thm. 9.17. Then:
`‖Σ_{j=1}^k U_k U_{k−1} ⋯ U_j p_1 − Σ_{j=1}^k U_1^{k+1−j} p_1‖ ≤ 2(k + 1)k‖H′‖²/(γ²N²) + O(k/N³)`."

What was changed: the printed error term `O(k/N³)` is given an explicit meaning. By Rem. 9.14
(p.214) the `O(·)` drops every factor not depending on `N`, so the constant `C` may depend on the
data `H, H′, H″, φ, γ, ‖H′‖, ‖H″‖, δ, T` but is quantified **before** `N` and `k`, with a threshold
`N₀`; the bound is required **uniformly** in `1 ≤ k ≤ N`. Why: as printed the `O(k/N³)` does not
say whether `k` is fixed as `N → ∞` (then "`k/N³`" is just `O(1/N³)`) or ranges up to `O(N)`. The
uniform reading is the one the source relies on: the proof of Thm. 9.17 applies the lemma at
`h = M − 1 = O(N)` and writes the remainder as `O(1/N²)` (p.221). The source's own induction
(Eqs. (9.29)–(9.32)) adds an `O(k/N³)` remainder at each step, which accumulates to `O(k²/N³)`, so
the printed proof does not by itself give this reading; the claim is stated as the lemma prints it.

Objects (Eqs. (9.9)–(9.11), (9.20), pp.213–219): `U_j = e^{i(T/N) H(j/N)}` (`NormedSpace.exp`),
`g_j = |φ(j/N)⟩` with the phase fixed by `⟨φ′(s)|φ(s)⟩ = 0`, and
`p_1 = Proj_{G₁^⊥}(g_0 − g_1) = (g_0 − g_1) − ⟨g_1|g_0 − g_1⟩ g_1`. The product
`U_k U_{k−1} ⋯ U_j` is `[U_k, U_{k−1}, …, U_j].prod`. The context of Thm. 9.17 is carried as in
`adiabatic_theorem_zero` (without the evolution `ψ`, which plays no role); `‖H′‖` is the bound
`N1`. -/
theorem adiabatic_unitary_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' H'' : ℝ → Matrix ι ι ℂ)
    (hH' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H t i j) (H' s i j) (Set.Icc 0 1) s)
    (hH'' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun t => H' t i j) (H'' s i j) (Set.Icc 0 1) s)
    (φ φ' : ℝ → EuclideanSpace ℂ ι)
    (hφ : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsState (φ s) ∧ act (H s) (φ s) = 0)
    (hφ' : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' s) (Set.Icc 0 1) s)
    (hphase : ∀ s ∈ Set.Icc (0 : ℝ) 1, inner ℂ (φ' s) (φ s) = 0)
    (γ : ℝ) (hγ : 0 < γ) (hgap : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (H s) 0 γ)
    (N1 N2 : ℝ) (hN1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H' s) ≤ N1)
    (hN2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, specNorm (H'' s) ≤ N2)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ)
    (hT : 10 ^ 3 / δ ^ 2 * max (N1 ^ 3 / γ ^ 4) (N1 * N2 / γ ^ 3) ≤ T) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ, 1 ≤ k → k ≤ N →
      let U : ℕ → Matrix ι ι ℂ := fun j =>
        NormedSpace.exp ((Complex.I * ((T / N : ℝ) : ℂ)) • H ((j : ℝ) / N))
      let g : ℕ → EuclideanSpace ℂ ι := fun j => φ ((j : ℝ) / N)
      let p1 : EuclideanSpace ℂ ι := (g 0 - g 1) - inner ℂ (g 1) (g 0 - g 1) • g 1
      ‖∑ j ∈ Finset.Icc 1 k, act ((List.range (k + 1 - j)).map fun i => U (k - i)).prod p1 -
          ∑ j ∈ Finset.Icc 1 k, act (U 1 ^ (k + 1 - j)) p1‖ ≤
        2 * ((k : ℝ) + 1) * k * N1 ^ 2 / (γ ^ 2 * (N : ℝ) ^ 2) + C * k / (N : ℝ) ^ 3 := by
  sorry

end QAlgorithms.Nannicini
