-- Prove2me | Theorems.Thm_PermutationStreams_Parity_correlation_bound
-- name    : PermutationStreams.Parity.correlation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:37.764207+00:00
-- url     : https://prove2.me/theorems/00a56a6b-3176-401f-84ba-66e3e9043482
-- title:
--   Theorem 4.2 — nonembeddable correlation bound (Bhangale–Braverman–Khot–Liu–Minzer)
-- statement:
--   Let $\Sigma,\Gamma,\Phi$ be finite sets, let $\mu$ be a probability distribution on $\Sigma\times\Gamma\times\Phi$ that is pairwise connected, and let $T:\operatorname{supp}(\mu)\to D$ be nonembeddable over the closed unit disk $D\subseteq\mathbb C$. Then there is a constant $\alpha=\alpha(\mu,T)>0$ such that for every positive integer $m$ and all $F:\Sigma^m\to D$, $G:\Gamma^m\to D$, $H:\Phi^m\to D$,
--
--   $$
--   \Bigl|\ \mathbb E_{(x,y,z)\sim\mu^{\otimes m}}\Bigl[F(x)\,G(y)\,H(z)\prod_{i=1}^m T(x_i,y_i,z_i)\Bigr]\Bigr|\le 2^{-\alpha m}.
--   $$
--
--   The constant depends only on $\mu$ and $T$, not on $m$ or on $F,G,H$. The theorem is the general three-player correlation bound used in the paper; specialized to the six-triple sign target it gives Lemma 4.3.
--
--   **Formalization Note** $T$ is a total complex-valued function required to lie in the disk at support points; its other values are multiplied by probability zero.
--
--   Differences from the source:
--   - encoding: T : supp(µ) → D → T : Σ × Γ × Φ → ℂ with ‖T t‖ ≤ 1 for µ(t) > 0; reason: off-support values carry probability zero in the expectation and do not enter nonembeddability
--   - encoding: probability distribution µ on Σ × Γ × Φ, expectation under µ^⊗m → a point-mass function µ with IsProbLaw µ, expectation the finite weighted sum prodExpect; reason: the same law and the same expectation on a finite set
--   - encoding: F : Σ^m → D, G : Γ^m → D, H : Φ^m → D, coordinates 1,…,m → complex-valued functions on Fin m → Σ, Fin m → Γ, Fin m → Φ with norm at most 1; reason: D is the closed unit disk; 0-based coordinates
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §4.2, p. 6, Theorem 4.2 (cited there as Theorem 2 of the full version of Bhangale, Braverman, Khot, Liu, Minzer, arXiv:2408.09352v1)

import Definitions.Def_PermutationStreams_Parity_Correlation

namespace PermutationStreams.Parity

/-- Braverman–Zamir, Theorem 4.2 (Bhangale, Braverman, Khot, Liu, Minzer), p.6. For a
pairwise connected probability law `μ` on a product of three finite sets and a target `T`
with values in the closed unit disk on `supp(μ)` that is nonembeddable over the disk, there is
`α = α(μ, T) > 0` such that for every `m ≥ 1` and all disk-valued `F, G, H`,
`|E_{μ^{⊗m}}[F(x) G(y) H(z) ∏ᵢ T(xᵢ, yᵢ, zᵢ)]| ≤ 2^{-αm}`. -/
theorem correlation_bound {Sig Gam Phi : Type} [Fintype Sig] [Fintype Gam] [Fintype Phi]
    (μ : Sig × Gam × Phi → ℝ) (hμ : IsProbLaw μ) (hconn : PairwiseConnected μ)
    (T : Sig × Gam × Phi → ℂ) (hT : ∀ t, 0 < μ t → ‖T t‖ ≤ 1)
    (hne : Nonembeddable μ T) :
    ∃ α : ℝ, 0 < α ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ (F : (Fin m → Sig) → ℂ) (G : (Fin m → Gam) → ℂ) (H : (Fin m → Phi) → ℂ),
        (∀ x, ‖F x‖ ≤ 1) → (∀ y, ‖G y‖ ≤ 1) → (∀ z, ‖H z‖ ≤ 1) →
        ‖prodExpect μ m (fun w =>
            F (fun i => (w i).1) * G (fun i => (w i).2.1) * H (fun i => (w i).2.2) *
              ∏ i, T (w i))‖
          ≤ (2 : ℝ) ^ (-(α * m)) := by sorry

end PermutationStreams.Parity
