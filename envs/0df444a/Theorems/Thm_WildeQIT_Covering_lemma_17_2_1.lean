-- Prove2me | Theorems.Thm_WildeQIT_Covering_lemma_17_2_1
-- name    : WildeQIT.Covering.lemma_17_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:56.711039+00:00
-- url     : https://prove2.me/theorems/4680e65f-1d59-4d8e-bfd2-277798422c6b
-- title:
--   Covering Lemma: $\Pr_{\mathcal C}\{\mathrm{oe}(\mathcal C)\le\varepsilon+4\sqrt\varepsilon+24\sqrt[4]\varepsilon\}\ge1-2D\exp(-\frac{\varepsilon^3}{4}\frac{|\mathcal M|d}{D})$
-- statement:
--   **Lemma 17.2.1 (Covering Lemma).** Let $\{p_X(x),\sigma_x\}_{x\in\mathcal X}$ be an ensemble of density operators on a finite-dimensional Hilbert space $\mathcal H$ over a finite alphabet $\mathcal X$, with expected density operator $\sigma=\sum_xp_X(x)\sigma_x$. Let $\Pi$ (the total subspace projector) and $\Pi_x$, $x\in\mathcal X$ (the codeword subspace projectors) be orthogonal projectors on $\mathcal H$ such that, for every $x\in\mathcal X$,
--
--   $$\operatorname{Tr}\{\sigma_x\Pi\}\ge1-\varepsilon,\qquad\operatorname{Tr}\{\sigma_x\Pi_x\}\ge1-\varepsilon,\qquad\operatorname{Tr}\{\Pi\}\le D,\qquad\Pi_x\sigma_x\Pi_x\le\frac1d\,\Pi_x,$$
--
--   where $\varepsilon\in(0,1)$, $D>0$, $d\in(0,D)$, and the last condition is in the operator (Loewner) order. Let $\mathcal M$ be a message set of size $|\mathcal M|$, and let a random covering code $\mathcal C=\{C_m\}_{m\in\mathcal M}$ consist of codewords $C_m$ drawn independently, each according to $p_X$; it gives the fake ensemble $\{1/|\mathcal M|,\sigma_{C_m}\}_{m\in\mathcal M}$ with fake expected density operator $\sigma(\mathcal C)=\frac1{|\mathcal M|}\sum_m\sigma_{C_m}$. Then the obfuscation error $\mathrm{oe}(\mathcal C)=\|\sigma(\mathcal C)-\sigma\|_1$ is small with high probability:
--
--   $$\Pr_{\mathcal C}\Bigl\{\mathrm{oe}(\mathcal C)\le\varepsilon+4\sqrt\varepsilon+24\sqrt[4]{\varepsilon}\Bigr\}\ge1-2D\exp\Bigl(-\frac{\varepsilon^3}{4}\,\frac{|\mathcal M|\,d}{D}\Bigr).$$
--
--   The covering lemma is the one-shot primitive behind privacy amplification in quantum Shannon theory: it is used for the private classical capacity, the quantum capacity, and state redistribution, where a small fake ensemble of size about $D/d$ must hide which message was sent.
--
--   **Formalization Note** $\mathcal H=\mathbb C^n$ for a finite index type $n$. Projectors satisfy $P^2=P=P^\dagger$. The traces $\operatorname{Tr}\{\sigma_x\Pi\}$, $\operatorname{Tr}\{\Pi\}$ are taken as real parts of the complex traces (they are real here). The message set is $\{0,\dots,K-1\}$ with $K=|\mathcal M|$; a code is a map from it to $\mathcal X$, and $\Pr_{\mathcal C}$ is the sum of the product weights $\prod_mp_X(c_m)$ over the codes satisfying the bound. $\mathrm{oe}$ uses the trace norm without the factor $\tfrac12$. The page's closing words "when $\varepsilon$ is small and $|\mathcal M|\gg\varepsilon^3d/D$" describe when the bound is useful and are not a hypothesis.
--
--   Differences from the source:
--   - encoding: a set $\mathcal M$ of size $|\mathcal M|$ and random codewords $C_m$ i.i.d. $\sim p_X$ → codes $c:\mathrm{Fin}\,K\to\mathcal X$ weighted by the published i.i.d. product distribution; reason: every finite message set is in bijection with $\mathrm{Fin}\,|\mathcal M|$, and the product weights are the law of the random code.
--   - encoding: operator inequality $\Pi_x\sigma_x\Pi_x\le\frac1d\Pi_x$ and real traces → positive semi-definiteness of $\frac1d\Pi_x-\Pi_x\sigma_x\Pi_x$ and real parts of complex traces; reason: definition of the Loewner order; the traces are real for these operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 17.2.1 (Covering Lemma), eqs. (17.11)-(17.15), p. 507

import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_iid
import Definitions.Def_WildeQIT_Covering_obfuscationError
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix
open scoped ComplexOrder
open Classical

namespace WildeQIT.Covering

/-- **Lemma 17.2.1 (Covering Lemma)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, eq. (17.15), p. 507). Let `{p_X(x), σ_x}_{x ∈ 𝒳}` be an ensemble of states
on `H`. Let `Π` (total subspace projector) and `Π_x`, `x ∈ 𝒳` (codeword subspace projectors) be
projectors onto subspaces of `H` with, for every `x`,
`Tr{σ_x Π} ≥ 1 − ε` (17.11), `Tr{σ_x Π_x} ≥ 1 − ε` (17.12), `Tr{Π} ≤ D` (17.13),
`Π_x σ_x Π_x ≤ (1/d) Π_x` (17.14), where `ε ∈ (0, 1)`, `D > 0`, `d ∈ (0, D)`. Let a random
covering code `C = {C_m}_{m ∈ M}` consist of `|M|` codewords chosen independently according to
`p_X`, with fake ensemble `{1/|M|, σ_{C_m}}`. Then
`Pr_C{oe(C) ≤ ε + 4√ε + 24 ε^{1/4}} ≥ 1 − 2D exp(−(ε³/4) |M| d / D)`.

**Formalization Note.** Finite dimensions and a finite alphabet, as throughout the book: `H = ℂⁿ`
for a finite index type `n`, `𝒳` a finite type, `p_X` the published `WildeQIT.FinDist`. Projectors
are `IsStarProjection` (`P² = P = P†`). Traces `Tr{σ_x Π}`, `Tr{Π}`, real here, are real parts of
complex traces; `≤` between operators is the Loewner order (`PosSemidef` difference). The message
set `M` is `Fin K` with `K = |M|`; a code is a map `c : Fin K → 𝒳`, and its probability under
i.i.d. choice is the published product distribution `p.iid K`; `Pr_C{·}` is `probOf` of the set of
good codes. `oe(C)` is `obfuscationError p σ c = ‖σ(C) − σ‖₁` with the unhalved trace norm.
`ε^{1/4}` is `ε ^ (1/4 : ℝ)`. The page's closing words "when ε is small and |M| ≫ ε³d/D" are
commentary on when the bound is useful; no such hypothesis is added. At `K = 0` the right side is
`1 − 2D < 0` (the hypotheses force `D ≥ Tr Π ≥ 1`), so that case is trivially true. -/
theorem lemma_17_2_1 {𝒳 n : Type} [Fintype 𝒳] [Fintype n] [DecidableEq n]
    (p : FinDist 𝒳) (σ : 𝒳 → Matrix n n ℂ) (hσ : ∀ x, IsDensityOperator (σ x))
    (P : Matrix n n ℂ) (Px : 𝒳 → Matrix n n ℂ)
    (hP : IsStarProjection P) (hPx : ∀ x, IsStarProjection (Px x))
    (ε D d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hD : 0 < D) (hd0 : 0 < d) (hdD : d < D)
    (h11 : ∀ x, 1 - ε ≤ (σ x * P).trace.re)
    (h12 : ∀ x, 1 - ε ≤ (σ x * Px x).trace.re)
    (h13 : P.trace.re ≤ D)
    (h14 : ∀ x, (((1 / d : ℝ) : ℂ) • Px x - Px x * σ x * Px x).PosSemidef)
    (K : ℕ) :
    1 - 2 * D * Real.exp (-(ε ^ 3 / 4) * (K * d / D)) ≤
      (p.iid K).probOf (Finset.univ.filter fun c : Fin K → 𝒳 =>
        obfuscationError p σ c ≤ ε + 4 * Real.sqrt ε + 24 * ε ^ ((1 : ℝ) / 4)) := by sorry

end WildeQIT.Covering
