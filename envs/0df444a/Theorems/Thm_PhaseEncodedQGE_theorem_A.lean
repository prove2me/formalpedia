-- Prove2me | Theorems.Thm_PhaseEncodedQGE_theorem_A
-- name    : PhaseEncodedQGE.theorem_A
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:51:49.306473+00:00
-- url     : https://prove2.me/theorems/48ff6ec3-1570-45b2-9fdc-b9e6631e2f28
-- title:
--   Theorem A — the first-order layer template, and determination of defect-layer histograms by the sorted readout
-- statement:
--   Let $G$ be a cubic graph on $n$ vertices, $t=\tan(\eta/2)$, $k_j=k_j(D)$.
--
--   **Part (1), template.** For every outcome $x$ with defect set $D$,
--   $$\lambda(x)=t^{-1}\sum_{j\notin D}h(k_j)-t\sum_{j\in D}h(k_j),$$
--   where $h=h^{X,r}$, $h^{X,r}(k)=\sum_{b=1}^r\cos(b\gamma(2k-3))$, for the X mixer at $r\ge1$ tied repetitions ($\cos(\gamma(2k-3))$ for one, $\cos(\gamma(2k-3))+\cos(2\gamma(2k-3))$ for two) and $h(k)=\sin(\gamma(2k-3))$ for the Y mixer. Under the Hadamard preparation (PE-QX1) the same holds with $t=1$, the profile $\sin(\gamma(2k-3))$ and the two sums exchanged:
--   $$\lambda(x)=\sum_{j\in D}\sin(\gamma(2k_j-3))-\sum_{j\notin D}\sin(\gamma(2k_j-3)).$$
--
--   **Part (2), determination** (with $0<\eta<\pi$ and $t>1$).
--
--   1. For the X mixer at $r\ge1$ repetitions, if $h(0)\ne h(1)$ and $t^2$ is irrational, then for every $m$ there is $\beta_0>0$ such that for all $\beta\in(0,\beta_0)$ and all cubic $G,H$ on $n$ vertices, equal sorted readouts on the ranks $K_{m-1}(n)+1,\dots,K_m(n)$ of the $m$-defect block imply equal histograms of $(E_{\mathrm{in}}(D),E_{\mathrm{out}}(D))$ over all $m$-subsets $D$.
--   2. For the Y mixer the same holds for the histogram of the odd readings when $\sin\gamma\ne0$ and $1,\sin^2\gamma,t^2,t^2\sin^2\gamma$ are linearly independent over $\mathbb Q$.
--   3. At the schedule $(\eta,\gamma)=(23/8,2)$, $t^2$ is transcendental and the independence holds, so both statements hold for every $n$: for PE-X1, PE-X2 and PE-Y1.
--
--   The sorted readout forgets the labelling of the vertices, so part (2) says that this label-free readout still recovers explicit graph invariants (the extremal-count and odd-reading histograms of every defect layer).
--
--   Differences from the source:
--   - generalization: the X-mixer members PE-X1, PE-X2 ($r\in\{1,2\}$) → every number $r\ge1$ of tied repetitions, $h=h^{X,r}$; reason: Theorem 3.2 and Corollary A.6 are stated for r tied repetitions and the proof uses only the evenness of h^{X,r}; r = 1, 2 are special cases
--   - encoding: $\lambda=p_1/p_0$ and $t^{\pm1}$ used without comment → hypotheses $\cos(\eta/2)\ne0$ and $\sin(\eta/2)\ne0$; reason: they exclude only the angles at which t, 1/t or p₁/p₀ is undefined (Lean's x/0 = 0 would otherwise give junk values)
--   - encoding: for all sufficiently small $\beta>0$ (for the given graphs) → one $\beta_0>0$ chosen before the cubic graphs $G,H$ on $\mathrm{Fin}\,n$; reason: for fixed n there are finitely many labelled graphs, so the uniform and the per-pair readings are the same claim
--   - reading: 'in part (2) let t = tan(η/2) > 1' → $0<\eta<\pi$ and $\tan(\eta/2)>1$; reason: §2 (p.5) puts 0 < η < π and t > 1 in force wherever layers, blocks and ranks are mentioned
--   - reading: 'Under the Hadamard preparation the same holds' → the Hadamard member PE-QX1 (X mixer, one repetition); reason: PE-QX1 is the only Hadamard-prepared member (§2, p.4) and Theorem 3.2 states the Hadamard case with one X mixer
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), Theorem A, §1.2, p.2 (PDF p.3) (= Theorems 3.2 and 3.3, pp.6–7)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_SortedReadout
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Theorem A, template and determination (Theorems 3.2 and 3.3) (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §1.2, p.2).

Let `G` be a cubic graph on `n` vertices under a degree-prepared member, and in part (2) let
`t = tan(η/2) > 1`, so that the sorted readout at `β = 0` lists the outcomes by defect count.

1. For every outcome `x` with defect set `D`,
   `λ(x) = t^{−1} ∑_{j∉D} h(k_j(D)) − t ∑_{j∈D} h(k_j(D))`, where the mixer profile `h` is
   `cos(γ(2k − 3))` for the X mixer, `sin(γ(2k − 3))` for the Y mixer, and
   `cos(γ(2k − 3)) + cos(2γ(2k − 3))` for two tied repetitions. Under the Hadamard preparation the
   same holds with `t = 1`, the profile `sin(γ(2k − 3))`, and the two sums exchanged.
2. For the X mixer, if `h(0) ≠ h(1)` and `t²` is irrational, then for every `m` and all sufficiently
   small `β > 0` the sorted readout on the ranks of the `m`-defect block determines the histogram of
   `(E_in(D), E_out(D))` over all `m`-subsets `D`. For the Y mixer the same holds for the histogram of
   the odd readings when `sin γ ≠ 0` and `1, sin² γ, t², t² sin² γ` are linearly independent over
   `ℚ`. At the schedule `t²` is transcendental and the independence holds, so both statements hold
   for every `n`.

**Formalization Note** The X mixer is stated at every number `r ≥ 1` of tied repetitions with
`h = h^{X,r}` (`r = 1, 2` are the paper's members PE-X1, PE-X2). Part (1) assumes only
`cos(η/2) ≠ 0 ≠ sin(η/2)`, which excludes the angles where `t^{±1}` or `λ = p₁/p₀` is undefined; the
Hadamard member is PE-QX1 (X mixer, one repetition). Part (2) keeps the standing assumption
`0 < η < π` of §2 (p.5). "Determines" is: one `β₀ > 0` such that for all `β ∈ (0, β₀)` and all cubic
`G, H` on `Fin n`, equal `m`-defect blocks (ranks `K_{m−1}(n)+1, …, K_m(n)` of the sorted readout)
imply equal histograms. The schedule is `(η, γ) = (23/8, 2)`; its clause covers PE-X1, PE-X2 and
PE-Y1. -/
theorem theorem_A :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (η γ : ℝ), Real.cos (η / 2) ≠ 0 →
      Real.sin (η / 2) ≠ 0 → ∀ r : ℕ, 1 ≤ r → ∀ x : Outcome n,
        firstOrder (degPrep G η) .X r G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hX r γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hX r γ (kdef G (defects x) j)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (η γ : ℝ), Real.cos (η / 2) ≠ 0 →
      Real.sin (η / 2) ≠ 0 → ∀ x : Outcome n,
        firstOrder (degPrep G η) .Y 1 G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hY γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hY γ (kdef G (defects x) j)) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsCubic G → ∀ (γ : ℝ) (x : Outcome n),
        firstOrder (hadPrep n) .X 1 G γ x =
          ∑ j ∈ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3)) -
            ∑ j ∈ Finset.univ \ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3))) ∧
    (∀ (n m r : ℕ), 1 ≤ r → ∀ (η γ : ℝ), 0 < η → η < Real.pi → 1 < Real.tan (η / 2) →
      hX r γ 0 ≠ hX r γ 1 → Irrational (Real.tan (η / 2) ^ 2) →
      ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .X r G γ β m = block (degPrep H η) .X r H γ β m →
        extremalHist G m = extremalHist H m) ∧
    (∀ (n m : ℕ) (η γ : ℝ), 0 < η → η < Real.pi → 1 < Real.tan (η / 2) → Real.sin γ ≠ 0 →
      LinearIndependent ℚ ![(1 : ℝ), Real.sin γ ^ 2, Real.tan (η / 2) ^ 2,
        Real.tan (η / 2) ^ 2 * Real.sin γ ^ 2] →
      ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .Y 1 G γ β m = block (degPrep H η) .Y 1 H γ β m →
        oddHist G m = oddHist H m) ∧
    (Transcendental ℚ (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
      LinearIndependent ℚ ![(1 : ℝ), Real.sin 2 ^ 2, Real.tan ((23 / 8 : ℝ) / 2) ^ 2,
        Real.tan ((23 / 8 : ℝ) / 2) ^ 2 * Real.sin 2 ^ 2] ∧
      ∀ n m : ℕ, ∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n),
        IsCubic G → IsCubic H →
        (block (degPrep G (23 / 8)) .X 1 G 2 β m = block (degPrep H (23 / 8)) .X 1 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .X 2 G 2 β m = block (degPrep H (23 / 8)) .X 2 H 2 β m →
          extremalHist G m = extremalHist H m) ∧
        (block (degPrep G (23 / 8)) .Y 1 G 2 β m = block (degPrep H (23 / 8)) .Y 1 H 2 β m →
          oddHist G m = oddHist H m)) := by sorry

end PhaseEncodedQGE
