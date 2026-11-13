-- Prove2me | Theorems.Thm_PhaseEncodedQGE_theorem_A_8
-- name    : PhaseEncodedQGE.theorem_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:51:31.121394+00:00
-- url     : https://prove2.me/theorems/360126c4-6768-4963-b9fd-0aba13c016fa
-- title:
--   Theorem A.8 — X-mixer layer determination of the $(E_{\mathrm{in}},E_{\mathrm{out}})$ histogram
-- statement:
--   Fix $m\ge1$ and $r\ge1$, angles with $0<\eta<\pi$, $t=\tan(\eta/2)>1$, and suppose $h_e\ne h_o$ (with $h_e=h^{X,r}(0)$, $h_o=h^{X,r}(1)$) and that either (a) $t^2>n-m$ or (b) $t^2$ is irrational. For cubic graphs on $n$ vertices with the degree-aware preparation and the X mixer at $r$ repetitions:
--
--   1. on the $m$-defect layer the first-order value determines the pair $(E_{\mathrm{in}}(D),E_{\mathrm{out}}(D))$;
--   2. under (a), two outcomes of the layer with different pairs have first-order values that differ by at least
--   $$|h_e-h_o|\,t^{-1}\min\{1,\;t^2-(n-m)\};$$
--   3. for all sufficiently small $\beta>0$, the sorted readout restricted to the ranks $K_{m-1}(n)+1,\dots,K_m(n)$ determines the histogram of $(E_{\mathrm{in}},E_{\mathrm{out}})$ over all $m$-subsets of $V(G)$: equal blocks for two cubic graphs imply equal histograms.
--
--   At the schedule $(\eta,\gamma)=(23/8,2)$, (b) holds for every $n$ ($\tan^2(23/16)$ is irrational) and (a) holds whenever $n-m<55.6$.
--
--   Differences from the source:
--   - generalization: the X-mixer members PE-X1, PE-X2 ($r\in\{1,2\}$) → every number $r\ge1$ of tied repetitions, $h=h^{X,r}$; reason: Theorem 3.2 and Corollary A.6 are stated for r tied repetitions and the proof uses only the evenness of h^{X,r}; r = 1, 2 are special cases
--   - generalization: outcomes of the layer of one graph G → outcomes of the layers of two cubic graphs G, G′ on the same n vertices; reason: taking G′ = G gives the paper's statement; the first-order value depends only on the profile, so the paper's argument is graph-independent
--   - encoding: for all sufficiently small $\beta>0$ (for the given graphs) → one $\beta_0>0$ chosen before the cubic graphs $G,H$ on $\mathrm{Fin}\,n$; reason: for fixed n there are finitely many labelled graphs, so the uniform and the per-pair readings are the same claim
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.2, p.15 (PDF p.16), Theorem A.8 (= Theorem 3.3(X), p.7)

import Mathlib
import Definitions.Def_PhaseEncodedQGE_SortedReadout
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Theorem A.8, layer determination for the X-mixer members (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), App. A.1.2, p.15).

Fix `m ≥ 1` and suppose `t > 1`, `h_e ≠ h_o` and that either (a) `t² > n − m` or (b) `t²` is
irrational. Then on the `m`-defect layer the first-order value `p₁(x)/p₀(x)` determines the pair
`(E_in(D), E_out(D))`. Under (a), two outcomes of the layer with different pairs have first-order
values that differ by at least `|h_e − h_o| t^{−1} min{1, t² − (n − m)}`. Consequently, for all
sufficiently small `β > 0`, the sorted readout restricted to the ranks `K_{m−1}(n) + 1, …, K_m(n)`
determines the histogram of `(E_in, E_out)` over all `m`-subsets of `V(G)`. At the schedule, (b)
holds for every `n` by Lemma A.7, and (a) holds for `n − m < 55.6`.

**Formalization Note** Degree-aware preparation, cubic graphs on `Fin n`, `0 < η < π` (the
standing assumption of §2, p.5), `h_e = h^{X,r}(0)`, `h_o = h^{X,r}(1)`, every `r ≥ 1`. The first
two clauses compare outcomes of two cubic graphs `G, G'` on the same vertex set (taking `G' = G` gives
the paper's single-graph reading). "Determines the histogram" is: one `β₀ > 0` such that for all
`β ∈ (0, β₀)` and all cubic `G, H`, equal blocks imply equal histograms. The schedule is
`(η, γ) = (23/8, 2)`, so `t² = tan²(23/16)`. -/
theorem theorem_A_8 :
    (∀ (n m r : ℕ), 1 ≤ m → 1 ≤ r → ∀ (η γ : ℝ), 0 < η → η < Real.pi →
      1 < Real.tan (η / 2) → hX r γ 0 ≠ hX r γ 1 →
      ((n : ℝ) - m < Real.tan (η / 2) ^ 2 ∨ Irrational (Real.tan (η / 2) ^ 2)) →
      (∀ G G' : SimpleGraph (Fin n), IsCubic G → IsCubic G' → ∀ x x' : Outcome n,
        (defects x).card = m → (defects x').card = m →
        firstOrder (degPrep G η) .X r G γ x = firstOrder (degPrep G' η) .X r G' γ x' →
        (Ein G (defects x), Eout G (defects x)) = (Ein G' (defects x'), Eout G' (defects x'))) ∧
      ((n : ℝ) - m < Real.tan (η / 2) ^ 2 →
        ∀ G G' : SimpleGraph (Fin n), IsCubic G → IsCubic G' → ∀ x x' : Outcome n,
          (defects x).card = m → (defects x').card = m →
          (Ein G (defects x), Eout G (defects x)) ≠ (Ein G' (defects x'), Eout G' (defects x')) →
          |hX r γ 0 - hX r γ 1| * (Real.tan (η / 2))⁻¹ *
              min 1 (Real.tan (η / 2) ^ 2 - ((n : ℝ) - m)) ≤
            |firstOrder (degPrep G η) .X r G γ x - firstOrder (degPrep G' η) .X r G' γ x'|) ∧
      (∃ β₀ > 0, ∀ β ∈ Set.Ioo 0 β₀, ∀ G H : SimpleGraph (Fin n), IsCubic G → IsCubic H →
        block (degPrep G η) .X r G γ β m = block (degPrep H η) .X r H γ β m →
        extremalHist G m = extremalHist H m)) ∧
    (Irrational (Real.tan ((23 / 8 : ℝ) / 2) ^ 2) ∧
      ∀ n m : ℕ, (n : ℝ) - m < 55.6 → (n : ℝ) - m < Real.tan ((23 / 8 : ℝ) / 2) ^ 2) := by sorry

end PhaseEncodedQGE
