-- Prove2me | Theorems.Thm_SubmodSparsify_step_3_union_bound
-- name    : SubmodSparsify.step_3_union_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:34.046922+00:00
-- url     : https://prove2.me/theorems/ce33630e-b26b-4f31-9820-7b4c7fd16e64
-- title:
--   §4.3, Step 3 — union bound over the increment dictionary: Lemma 3.1 fails for some increment with probability $< \delta/2$
-- statement:
--   Let $f_1, \dots, f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ be submodular with $f_i(\emptyset) = f_i([n]) = 0$, with Algorithm 1's weights $p_i$, and let $\varepsilon, \delta \in (0,1)$ and $\Lambda := 56\varepsilon^{-2}\log(32n/\delta)$. Sample each component independently with probability $\min\{1, \Lambda p_i\}$ and weight $w_i = 1/\min\{1, \Lambda p_i\}$ (else $w_i = 0$).
--
--   Call an **increment vector** any $z = (z_1, \dots, z_m)$ with $z_i = f_i^{\to}(I, O) - f_i^{\to}(I', O')$ for sets $I' \subseteq I$, $O' \subseteq O$ with $I \cap O = \emptyset$ and $\ell := |I| + |O| \in [n]$. Then
--
--   $$\Pr\Bigl[\exists \text{ increment vector } z:\ \Bigl|\sum_{i=1}^m (w_i - 1) z_i\Bigr| > \frac{\varepsilon}{2}\sum_{i=1}^m z_i + \frac{2\ell \log(32n/\delta)}{\varepsilon\Lambda} \max_{i \in [m]} \frac{z_i}{p_i}\Bigr] < \frac{\delta}{2}.$$
--
--   The right-hand side is Lemma 3.1's threshold with $\eta = \varepsilon/2$ and $x = \ell\log(32n/\delta)$; there are at most $\binom{n}{\ell}4^\ell \le (4n)^\ell$ increment vectors of each size $\ell$.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: standing assumption of §4 (p.18): every component normalized, f_i(∅) = f_i([n]) = 0, nonnegative submodular → explicit hypotheses hf0, hsub, hempty, huniv; reason: the section's standing hypotheses written as binders; same instances
--   - reading: "the probability that Lemma 3.1 fails for any increment vector in ⋃_ℓ D_ℓ is at most … < δ/2" → the probability of the event that Lemma 3.1's inequality (η = ε/2, x = ℓ log(32n/δ)) is violated for some increment vector is < δ/2; reason: the failure event of Lemma 3.1 written out
--   - encoding: max_i z_i/p_i, sampling law, w_i → ⨆ i, z_i / p_i with Lean division; bernProb, sampledWeight with Λ = samplingScale n ε δ; reason: components with p_i = 0 have z_i = 0 and contribute 0 to every term
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), proof of Theorem 4.1, §4.3, Step 3, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights
import Definitions.Def_SubmodSparsify_bernProb

namespace SubmodSparsify

/-- **§4.3, Step 3** (p.27): the union bound over the increment dictionary.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), proof of Theorem 4.1, §4.3, Step 3, p.27.

With `pᵢ` the weights of Algorithm 1, `ε, δ ∈ (0, 1)` and `Λ = 56ε⁻² log(32n/δ)`, the
probability that Lemma 3.1 (with `η = ε/2`, `x = ℓ log(32n/δ)`) fails for some increment vector
`zᵢ = f→ᵢ(I, O) − f→ᵢ(I′, O′)` with `I′ ⊆ I`, `O′ ⊆ O`, `I ∩ O = ∅` and `|I| + |O| = ℓ ∈ [n]`, i.e.
that `|Σᵢ (wᵢ − 1)zᵢ| > (ε/2)Σᵢ zᵢ + 2ℓ log(32n/δ) maxᵢ(zᵢ/pᵢ)/(εΛ)` for one of them, is less
than `δ/2`.

**Formalization Note.** `[n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ`
(paper indices = values + 1), `S̄ = Sᶜ`. The hypotheses on `f` are those of Theorem 4.1, the
standing assumption of §4 (p.18): nonnegative, submodular, `fᵢ(∅) = fᵢ([n]) = 0`. `inShare f u i`
is `s_i^{(u)}`, `outShare f v i` is `t_i^{(v)}`, `weights f i` is `pᵢ`, `influence f S w` is
`inf_S(w)` of (25), `residual f i S U` is `Δᵢ(S, U)` of (24) (module `SubmodSparsify.weights`). The sample `ξ`, its law and the weights `wᵢ` are those of module
`SubmodSparsify.bernProb` with `Λ = samplingScale n ε δ`. The right-hand side is Lemma 3.1's
`ηΣz + xR/(ηΛ)` at `η = ε/2`, `x = ℓ log(32n/δ)`, `R = ⨆ i, zᵢ/pᵢ` (Lean division, `x/0 = 0`).
`ℓ ∈ [n]` is `1 ≤ |I| + |O|` (`|I| + |O| ≤ n` holds for disjoint `I`, `O`). -/
theorem step_3_union_bound {n m : ℕ} (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
    (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
    (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    bernProb (sampleProb (weights f) (samplingScale n ε δ)) (fun ξ =>
      ∃ I O I' O' : Finset (Fin n), I' ⊆ I ∧ O' ⊆ O ∧ Disjoint I O ∧ 1 ≤ I.card + O.card ∧
        ε / 2 * ∑ i, (blockMinCut (f i) I O - blockMinCut (f i) I' O') +
            2 * ((I.card + O.card : ℕ) : ℝ) * Real.log (32 * n / δ) *
              (⨆ i, (blockMinCut (f i) I O - blockMinCut (f i) I' O') / weights f i) /
              (ε * samplingScale n ε δ) <
          |∑ i, (sampledWeight (weights f) (samplingScale n ε δ) ξ i - 1) *
            (blockMinCut (f i) I O - blockMinCut (f i) I' O')|) < δ / 2 := by sorry

end SubmodSparsify
