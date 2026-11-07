-- Prove2me | Theorems.Thm_RegevRecon_reconstruction_link
-- name    : RegevRecon.reconstruction_link
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:55.392958+00:00
-- url     : https://prove2.me/theorems/1cd6e5c7-73e1-46d1-99bf-d676a99f9009
-- title:
--   (48), (50) — the posterior recursion and the threshold in recursion form
-- statement:
--   Fix the parameters. For every $\beta\ge0$:
--
--   1. $\tilde\eta^{(\ell)}$ of (48) has the law of the posterior error vector $z\mapsto\Pr[X_i=x_i^*+z/c_0\mid\text{data below }i]$ of a variable with $D-1$ child constraints, planted value $x_i^*$ and coefficient $c_0$ on its parent constraint;
--   2. $\Psi_\ell$ and $I_\ell$ are nonincreasing in $\ell$, and their limits exist;
--   3. $\Psi_\infty=0$ if and only if $\lim_\ell I_\ell=0$.
--
--   Hence the threshold (46) can be written in the recursion form
--
--   $$
--   \beta_{\mathrm{dyn}}=\inf\{\beta>0:\Psi_\infty(\beta)>0\}\qquad(50).
--   $$
--
--   This connects the information-theoretic definition of $\beta_{\mathrm{dyn}}$ with the recursion the proof of Theorem 4 uses.
--
--   Differences from the source:
--   - reading: (48) "to obtain the posterior distribution at generation ℓ" → the posterior of a variable with D − 1 child constraints under the uniform prior, given its tuple and the data below it; reason: the recursion has D − 1 factors and rescales by the parent coefficient, as Figure 3, p.19 describes
--   - reading: "As noted in [MM06], the limit Ψ_∞ exists and vanishes exactly when the mutual information vanishes" → stated for I_ℓ with a root of D child constraints, while the recursion has D − 1; reason: p.4 and Figure 3 give the root D constraints; given X₀ and T the D branches are independent, so the equivalence carries over
--   - generalization: Ψ_ℓ is nonincreasing and Ψ_∞ exists (the page states no monotonicity of I_ℓ) → also I_ℓ is nonincreasing in ℓ and lim_ℓ I_ℓ exists; reason: the same data-processing argument (the deeper boundary and tree data are a continuation independent of the root given the nearer boundary), and (46) presupposes the limit; the added clauses only add content, so the statement specializes to the source's claim
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
--   - encoding: thresholds with inf ∅ = ∞ and lim > 0 → thresholds in ℝ≥0∞; lim > 0 is ¬Tendsto · atTop (𝓝 0); reason: for a nonnegative sequence with a limit the two agree, and the limits exist by milestones
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §7, (48)–(50), pp.19–20

import Mathlib
import Definitions.Def_RegevRecon_etaLaw
import Definitions.Def_RegevRecon_reconInfo

namespace RegevRecon

open Filter Topology

/-- **The reconstruction link**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), §7, pp.19–20: at every `β ≥ 0`,
(a) `η̃^(ℓ)` of (48) has the law of the posterior error vector of a variable with `D − 1` child constraints;
(b) `Ψ_ℓ` is nonincreasing, `I_ℓ` is nonincreasing, and both limits exist;
(c) `Ψ_∞` vanishes exactly when the mutual information limit vanishes; hence the threshold (46) equals (50),
`β_dyn = inf {β > 0 : Ψ_∞ > 0}`.

**Formalization Note** The root of `I_ℓ` has `D` child constraints, while the recursion (48) has `D − 1`
(Figure 3, p.19). The paper cites [MM06] for (c); the page does not spell out the `D` vs `D − 1` step, so it is
part of this statement. Antitonicity and the limit are stated for `ℓ ≥ 0`. -/
theorem reconstruction_link {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ) :
    (∀ β : ℝ, 0 ≤ β →
      (∀ ℓ, posteriorLaw k D S Λ β ℓ = etaLaw k D S Λ β ℓ) ∧
      Antitone (Psi k D S Λ β) ∧ Antitone (reconInfo k D S Λ β) ∧
      (∃ L, Tendsto (Psi k D S Λ β) atTop (𝓝 L)) ∧
      (∃ L, Tendsto (reconInfo k D S Λ β) atTop (𝓝 L)) ∧
      (Tendsto (Psi k D S Λ β) atTop (𝓝 0) ↔ Tendsto (reconInfo k D S Λ β) atTop (𝓝 0))) ∧
    betaDyn k D S Λ =
      sInf (ENNReal.ofReal '' {β : ℝ | 0 < β ∧ ¬ Tendsto (Psi k D S Λ β) atTop (𝓝 0)}) := by sorry

end RegevRecon
