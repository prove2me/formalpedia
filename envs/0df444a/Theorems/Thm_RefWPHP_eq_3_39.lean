-- Prove2me | Theorems.Thm_RefWPHP_eq_3_39
-- name    : RefWPHP.eq_3_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:01:48.696731+00:00
-- url     : https://prove2.me/theorems/3f31f3d2-0c36-41ca-8054-b8f8f0552360
-- title:
--   Eq. (3.39) — substitution step: a PK$_d$ refutation and a derivation of the substituted axioms give a PK$_{d+2}$ refutation with size linear in $T$
-- statement:
--   Let $\Phi$ be a set of cedents over variables $V$, $\Psi$ a set of cedents over variables $V'$, and $\sigma$ a substitution of formulas over $V'$ for the variables $V$ with $\mathrm{depth}(\sigma(x)) \le 2$ and $\mathrm{size}(\sigma(x)) \le S$ for all $x$. Suppose $\Phi$ has a PK$_d$-refutation of size at most $T$, and $\Psi$ has a PK$_{d+2}$-derivation of size at most $P$ that contains $\Gamma{\restriction}\sigma$ for every $\Gamma \in \Phi$. Then $\Psi$ has a PK$_{d+2}$-refutation of size
--
--   $$
--   \le P + T \cdot (S + 2)^{c_0},
--   $$
--
--   where $c_0$ is an absolute constant, fixed before all the data.
--
--   With $\Phi = \mathrm{Ref}_s(\varphi)$, $\Psi = \mathrm{PHP}^L_W$ and $\sigma = \sigma_{\pi,s}$, this is the composition $\mathrm{PHP}^L_W \vdash_{\mathrm{PK}_2} \mathrm{Ref}_s(\varphi){\restriction}\sigma_{\pi,s} \vdash_{\mathrm{PK}_{d+2}} \bot$ displayed in the proof of Theorem 3.2, and the size bound is what makes the blow-up linear in $T$.
--
--   Differences from the source:
--   - generalization: Φ = Ref_s(φ), Ψ = PHP^L_W, σ = σ_{π,s}, first half in PK_2 → any Φ, Ψ, any σ with images of depth at most 2 and size at most S, first half in PK_{d+2}; reason: the page's composition is the instance; a PK_2-derivation is a PK_{d+2}-derivation
--   - reading: the size blow-up is bounded by T · poly(L, D, s, n, m) → size at most P + T · (S + 2)^c₀ with c₀ absolute; reason: P and S are polynomial in those parameters for σ_{π,s}, and T ≥ 1, so this gives the page's bound
--   - encoding: size is the length of a binary string (p.15) → symbol count plus one per line (derivSize); reason: the two differ by at most a logarithmic factor in the number of variables, which the polynomial absorbs
--   - reading: binary ∧-Intro and ∨-Intro on unbounded fan-in formulas, used in one step as "repeated ∧-introduction"; Cut on φ₁ ∧ ⋯ ∧ φ_m; cedents are sequences → PKStep: n-ary ∧/∨-introduction (0-ary ∧ gives ⊤), Atomic LEM, weakening to any list containing the premise, Cut on one formula and on a conjunction, hypotheses from Φ; dag-like lines; reason: ⊤ and ⊥ occur as formulas in (3.2)–(3.3), PK_0 must be Resolution (p.15), and the page counts repeated introductions as one step
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), eq. (3.39), p.26 (PDF p.28), proof of Theorem 3.2

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation

namespace RefWPHP

open PKFormula

/-- Eq. (3.39), p.26 (PDF 28), of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole
Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), the composition step of the
proof of Theorem 3.2: `PHP^L_W ⊢_{PK_2} Ref_s(φ)↾σ_{π,s} ⊢_{PK_{d+2}} ⊥`, "the second half is
obtained by substituting `σ_{π,s}` in the PK_d-refutation of `Ref_s(φ)` to get a
PK_{d+2}-refutation of `Ref_s(φ)↾σ_{π,s}`", with a size blow-up linear in the size `T` of the
PK_d-refutation.

Stated for any sets of cedents `Φ` (over `V`) and `Ψ` (over `V'`) and any substitution `σ` whose
images have depth at most 2 and size at most `S`: a PK_d-refutation of `Φ` of size at most `T` and
a PK_{d+2}-derivation from `Ψ` of size at most `P` containing every cedent of `Φ↾σ` give a
PK_{d+2}-refutation of `Ψ` of size at most `P + T·(S + 2)^c₀`, with `c₀` absolute.

**Formalization Note.** `Φ = Ref_s(φ)`, `Ψ = PHP^L_W`, `σ = σ_{π,s}` is the instance used in the
proof; `S` is a bound on the sizes of the images of `σ`. -/
theorem eq_3_39 : ∃ c₀ : ℕ, ∀ {V V' : Type} (Φ : Set (Cedent V)) (Ψ : Set (Cedent V'))
    (σ : V → PKFormula V') (d S T P : ℕ),
    (∀ x, depth (σ x) ≤ 2) → (∀ x, size (σ x) ≤ S) →
    (∃ ρ : List (Cedent V), IsPKRefutation d Φ ρ ∧ derivSize ρ ≤ T) →
    (∃ ρ : List (Cedent V'), IsPKDerivation (d + 2) Ψ ρ ∧
      (∀ Γ ∈ Φ, Γ.map (subst σ) ∈ ρ) ∧ derivSize ρ ≤ P) →
    ∃ ρ' : List (Cedent V'), IsPKRefutation (d + 2) Ψ ρ' ∧
      derivSize ρ' ≤ P + T * (S + 2) ^ c₀ := by sorry

end RefWPHP
