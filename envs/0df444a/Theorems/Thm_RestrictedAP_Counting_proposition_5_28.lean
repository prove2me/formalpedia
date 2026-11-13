-- Prove2me | Theorems.Thm_RestrictedAP_Counting_proposition_5_28
-- name    : RestrictedAP.Counting.proposition_5_28
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:55.049752+00:00
-- url     : https://prove2.me/theorems/8b024fec-04e9-4fdb-b0ba-d56866ca8694
-- title:
--   Proposition 5.28 — no $\mathbb Z$-embedding makes the covariance of the non-constant basis functions uniformly positive definite
-- statement:
--   For every $q\ge1$ and $\alpha>0$ there is $\eta=\eta_{\alpha,q}>0$ such that the following holds. Let $|\Sigma|=q$ and let $\mu$ be a distribution on $\Sigma^3$ whose support has no $\mathbb Z$-embedding, whose minimum non-zero atom probability is $\alpha$, and whose marginals $\mu_1,\mu_2,\mu_3$ each have full support on $\Sigma$. For $i\in\{1,2,3\}$ let $f^{(i)}_0=1,f^{(i)}_1,\dots,f^{(i)}_{q-1}$ be an orthonormal basis of $L^2(\Sigma,\mu_i)$, let
--   $$W=\big(f^{(1)}_1(X),\dots,f^{(1)}_{q-1}(X),\ f^{(2)}_1(Y),\dots,f^{(2)}_{q-1}(Y),\ f^{(3)}_1(Z),\dots,f^{(3)}_{q-1}(Z)\big)\in\mathbb C^{3(q-1)}$$
--   for $(X,Y,Z)\sim\mu$, and $M=\mathbb E_\mu[WW^*]$. Then $M$ is Hermitian positive definite, and $M-\eta I\succeq0$.
--
--   In the proof of Theorem 1.4 this is what makes Theorem 5.11 applicable with a constant depending only on $\alpha$ and $|\Sigma|$.
--
--   **Formalization Note.** $q=q'+1$; $W$ is indexed by $(i,j)\in$ `Fin 3 × Fin q'`, carrying $f^{(i)}_{j+1}$; orthonormality is $\sum_a\mu_i(a)\overline{f^{(i)}_j(a)}f^{(i)}_k(a)=[j=k]$; $M_{(i,j),(k,l)}=\sum_t\mu(t)W_{(i,j)}(t)\overline{W_{(k,l)}(t)}$.
--
--   Differences from the source:
--   - reading: M − η_{α,|Σ|} I ⪰ 0 for some η_{α,|Σ|} > 0 → ∃ η > 0 after q = |Σ| and α, before Σ, μ and the bases; reason: the subscript: η depends only on α and |Σ| (the closing compactness sentence of the proof)
--   - encoding: q = |Σ| and indices 1..q−1, the vector in ℂ^{3(q−1)} → |Σ| = q′ + 1, basis indexed by Fin (q′+1) with index 0 the constant 1, W indexed by Fin 3 × Fin q′; reason: Σ is nonempty because μ is a distribution
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), pp. 48–49, Proposition 5.28

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

open ComplexOrder

namespace RestrictedAP.Counting

/-- **Proposition 5.28** (pp. 48–49). For every `q ≥ 1` (written `q = q' + 1`) and `α > 0` there is
`η = η_{α,q} > 0` such that: let `Σ` have `|Σ| = q`, let `μ` be a distribution on `Σ^3` whose
support has no `ℤ`-embedding and whose minimum non-zero atom probability is `α`, and whose three
marginals `μ_1, μ_2, μ_3` have full support on `Σ`. For `i ∈ {1,2,3}` let
`f^{(i)}_0 = 1, f^{(i)}_1, …, f^{(i)}_{q−1}` be an orthonormal basis of `L²(Σ, μ_i)`, let
`W = (f^{(1)}_1(X), …, f^{(1)}_{q−1}(X), f^{(2)}_1(Y), …, f^{(3)}_{q−1}(Z)) ∈ ℂ^{3(q−1)}` for
`(X, Y, Z) ∼ μ`, and let `M = E_μ[W W^*]`. Then `M` is Hermitian positive definite and
`M − η I ⪰ 0`.

Encoding: coordinates of `W` are indexed by `(i, j) ∈ Fin 3 × Fin q'` and carry
`f^{(i)}_{j+1}`; `⟨g, h⟩_{μ_i} = Σ_a μ_i(a) · conj(g a) · h a`. -/
theorem proposition_5_28 (q' : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig = q' + 1 →
      ∀ μ : Sig × Sig × Sig → ℝ, IsDist μ → ¬ DistHasEmbedding ℤ μ → IsMinAtom μ α →
        (∀ (i : Fin 3) (a : Sig), marginal μ i a ≠ 0) →
      ∀ fb : Fin 3 → Fin (q' + 1) → Sig → ℂ,
        (∀ i a, fb i 0 a = 1) →
        (∀ (i : Fin 3) (j k : Fin (q' + 1)),
          ∑ a, (marginal μ i a : ℂ) * star (fb i j a) * fb i k a = if j = k then 1 else 0) →
        let W : Fin 3 × Fin q' → Sig × Sig × Sig → ℂ :=
          fun ij t => fb ij.1 ij.2.succ (coord3 ij.1 t)
        let Mcov : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ :=
          Matrix.of fun ij kl => ∑ t, (μ t : ℂ) * W ij t * star (W kl t)
        Mcov.PosDef ∧
          (Mcov - (η : ℂ) • (1 : Matrix (Fin 3 × Fin q') (Fin 3 × Fin q') ℂ)).PosSemidef := by sorry

end RestrictedAP.Counting
