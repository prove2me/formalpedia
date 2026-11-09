-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_6_4
-- name    : ResultantVNP.lemma_2_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:41.555973+00:00
-- url     : https://prove2.me/theorems/37909ca2-1afc-4ce3-86ca-5fa34e916d74
-- title:
--   Lemma 2.6(4) — simultaneous permutation
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n$ be homogeneous forms of equal degree $e\ge1$. For every permutation $\sigma\in S_n$, with $x_\sigma=(x_{\sigma(1)},\dots,x_{\sigma(n)})$,
--
--   $$
--   \mathrm{Res}\big(f_{\sigma(1)}(x_\sigma),\dots,f_{\sigma(n)}(x_\sigma)\big)=\mathrm{Res}\big(f_1(x),\dots,f_n(x)\big).
--   $$
--
--   **Formalization Note** $f(x_\sigma)$ is $f$ with $x_k$ renamed to $x_{\sigma(k)}$.
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1 and e ≥ 1; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: Res(f₁, …, fₙ) of homogeneous forms → resOf 𝓡 d f: Res_d evaluated at the coefficients [x^e] f_i, |e| = d_i, with each f_i assumed homogeneous of degree d_i; reason: the notation of Definition 2.1 (evaluation at the coefficients of the forms)
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.6(4), p.13

import Mathlib
import Definitions.Def_ResultantVNP_resOf

namespace ResultantVNP

/-- **Lemma 2.6(4) (Simultaneous permutation).** Let `f₁, …, fₙ` be homogeneous forms of equal degree
`e`. For every permutation `σ ∈ S_n`, with `x_σ = (x_{σ(1)}, …, x_{σ(n)})`,
`Res(f_{σ(1)}(x_σ), …, f_{σ(n)}(x_σ)) = Res(f₁(x), …, fₙ(x))`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.6(4), p.13.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `f(x_σ)` is `rename σ f` (`x_k ↦ x_{σ(k)}`). `n ≥ 1`, `e ≥ 1`. -/
theorem lemma_2_6_4 (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (e : ℕ) (he : 0 < e)
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, (f i).IsHomogeneous e)
    (σ : Equiv.Perm (Fin n)) :
    resOf 𝓡 (fun _ => e) (fun i => MvPolynomial.rename σ (f (σ i))) = resOf 𝓡 (fun _ => e) f := by sorry

end ResultantVNP
