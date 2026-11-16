-- Prove2me | Theorems.Thm_ROLDescent_Supplement_theorem_6_4
-- name    : ROLDescent.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:57:36.432769+00:00
-- url     : https://prove2.me/theorems/4d185842-838a-4dd9-bdcc-c683fed6e303
-- title:
--   Theorem 6.4 — binary influence and increment Gram: $C^{\mu_{S,s}}=\hat\Sigma^{\mu_{S,s}}$ and $\theta_S=(1+\max_s\lambda_{\max}(\Psi^{\mu_{S,s}}))/m$
-- statement:
--   Let $V$ be a finite set of $n$ sites and $\mu$ a full-support probability law on the binary configurations $\{0,1\}^V$ ($\mu(x)>0$ for every $x$). Fix $S\subseteq V$ with $m=n-|S|\ge2$ remaining sites. For an assignment $s\in\{0,1\}^S$ write $\mu_{S,s}=\mu(\,\cdot\mid X_S=s)$, let $\Sigma^{\mu_{S,s}}$ be the conditional covariance matrix of the spins outside $S$, $D^{\mu_{S,s}}$ its diagonal of conditional variances, $\hat\Sigma^{\mu_{S,s}}=(D^{\mu_{S,s}})^{-1/2}\Sigma^{\mu_{S,s}}(D^{\mu_{S,s}})^{-1/2}$ the normalized covariance matrix (113), $\Psi^{\mu_{S,s}}$ the signed influence matrix (112), and $C^{\mu_{S,s}}$ the Gram matrix in $L^2(\mu_{S,s})$ of the normalized centered spins $u_i=(X_i-\mathbb E_{\mu_{S,s}}X_i)/\sqrt{\operatorname{Var}_{\mu_{S,s}}(X_i)}$, $i\notin S$. Let $\theta_S$ be the Gram norm of the observable hierarchy $I_S=\{f:\mathbb E_\mu[f\mid X_S]=0\}$ in $L^2(\mu)$ with the complete uniform weights $1/m$. Then:
--
--   1. **Increment Gram.** For every $s\in\{0,1\}^S$,
--   $$C^{\mu_{S,s}}=\hat\Sigma^{\mu_{S,s}} .\tag{114}$$
--   2. **Influence.** For every $s\in\{0,1\}^S$, the signed influence matrix is similar to $\hat\Sigma^{\mu_{S,s}}-I$:
--   $$\hat\Sigma^{\mu_{S,s}}-I=(D^{\mu_{S,s}})^{1/2}\,\Psi^{\mu_{S,s}}\,(D^{\mu_{S,s}})^{-1/2}.$$
--   3. **Gram–influence identity.**
--   $$\theta_S=\frac{1+\max_{s}\lambda_{\max}\big(\Psi^{\mu_{S,s}}\big)}{m}.\tag{115}$$
--
--   The identity (115) turns spectral-independence bounds on the influence matrices into levelwise Gram bounds for the descent theorem, which is how the paper recovers the spectral-independence gap product for Glauber dynamics.
--
--   **Formalization Note** $L^2(\mu)$ is represented in `EuclideanSpace ℂ (V → Bool)` through the unitary $f\mapsto\sqrt\mu f$; $\theta_S$ is the published `ROLDescent.gramNorm` on the complete complex $2^V$ with one unit facet, which gives the weights $1/m$. The maximum over $s$ is a supremum over the finite type of assignments.
--
--   Differences from the source:
--   - encoding: binary spins X_i ∈ {0,1}, configurations {0,1}^V, assignments s ∈ {0,1}^S → configurations V → Bool, assignments S → Bool, spin value 1 ↔ true; reason: the same finite sets
--   - encoding: K = L²(µ) with ⟨f,g⟩_µ = Σ_x µ(x) conj(f x) g x → EuclideanSpace ℂ (V → Bool) via the unitary f ↦ √µ·f; I_S as the kernels of ψ ↦ Σ_{x_S = s} √µ(x) ψ(x); reason: under full support the map is a unitary isomorphism, so projections, the removed spaces and operator norms are those of L²(µ)
--   - encoding: θ_S of (75) with π_S(i) = 1/m in the complete site hierarchy → published ROLDescent.gramNorm on the complex Finset.univ.powerset with d = |V| and weight 1 on the facet V; reason: on that complex the link of S is V ∖ S and π_S(i) = 1/(n − |S|) = 1/m (checked in the sanity file)
--   - encoding: max over assignments s of λ_max(Ψ^{µS,s}); λ_max the largest eigenvalue of Ψ → ⨆ over the finite nonempty type S → Bool; lambdaMax = sSup of the real eigenvalues with real eigenvectors; reason: a finite maximum; Ψ is similar to a real symmetric matrix, so its eigenvalues are real with real eigenvectors and the sSup is the maximum
--   - encoding: m = n − |S| ≥ 2 → S.card + 2 ≤ Fintype.card V, m = ((card V − S.card : ℕ) : ℝ); reason: the natural subtraction is exact under the hypothesis
--   - encoding: (114) C^{µS,s} = Σ̂^{µS,s} → incrGram μ S s = (normCov μ S s).map (↑· : ℝ → ℂ); reason: observables are ℂ-valued, so the Gram matrix is complex, while Σ̂ is a real matrix; comparing after the entrywise real-to-complex cast is the same equation
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, eqs. (112)–(115), p.50 (PDF 50); setting Section 6.2.1, pp.46–47

import Mathlib
import Definitions.Def_ROLDescent_Supplement_normCov
import Definitions.Def_ROLDescent_Supplement_influence
import Definitions.Def_ROLDescent_Supplement_incrGram
import Definitions.Def_ROLDescent_Supplement_lambdaMax
import Definitions.Def_ROLDescent_Supplement_siteGramNorm

namespace ROLDescent.Supplement

/-- **Theorem 6.4 (Binary influence and increment Gram).**
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, eqs. (113)–(115), p.50 (PDF 50), with the setting of Section 6.2.1 (p.46–47) and
Section 6.2.2 (p.50): µ is a full-support probability law on `{0,1}^V`; "Fix S, s with
m = n − |S| ≥ 2 remaining sites."

For every assignment `s ∈ {0,1}^S`:
1. (114) the Gram matrix `C^{µS,s}` in `L²(µS,s)` of the normalized centered spins equals the
   normalized covariance matrix `Σ̂^{µS,s}`;
2. `Σ̂^{µS,s} − I = (D^{µS,s})^{1/2} Ψ^{µS,s} (D^{µS,s})^{−1/2}`;
and (115) the Gram norm of the observable hierarchy (108) satisfies
`θ_S = (1 + max_s λ_max(Ψ^{µS,s})) / m`.

**Formalization Note** Configurations are `V → Bool`; `n = Fintype.card V`; `m ≥ 2` is
`S.card + 2 ≤ n`, and `m` is cast to ℝ after the (then exact) natural subtraction. `D^{1/2}` is the
diagonal of `√Var_{µS,s}(X_i)`, `Var = condCov μ S s i i`. The maximum over `s` is a `⨆` over the
finite nonempty type `S → Bool`. `θ_S` is `siteGramNorm` (the published `gramNorm` on the complete
hierarchy with weights `1/m`), not `‖Σ̂‖`. -/
theorem theorem_6_4 {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (hμ_pos : ∀ x, 0 < μ x) (hμ_sum : ∑ x, μ x = 1) (S : Finset V)
    (hm : S.card + 2 ≤ Fintype.card V) :
    (∀ s : S → Bool, incrGram μ S s = (normCov μ S s).map (fun r : ℝ => (r : ℂ))) ∧
    (∀ s : S → Bool, normCov μ S s - 1 =
      Matrix.diagonal (fun i => Real.sqrt (condCov μ S s i i)) * influence μ S s *
        Matrix.diagonal (fun i => (Real.sqrt (condCov μ S s i i))⁻¹)) ∧
    siteGramNorm μ S =
      (1 + ⨆ s : S → Bool, lambdaMax (influence μ S s)) / ((Fintype.card V - S.card : ℕ) : ℝ) := by sorry

end ROLDescent.Supplement
