-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_theorem_4_2
-- name    : ScatPoly.Inequiv.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:50.267667+00:00
-- url     : https://prove2.me/theorems/9b619102-c849-4bd6-a63d-0db48a590e38
-- title:
--   Theorem 4.2 (a)–(b), p. 16, U_h form — U_h, U_k ΓL(2, q^n)-equivalent iff h = ±k^ρ (t ≢ 2) or h = ℓk^ρ (t ≡ 2 mod 4)
-- statement:
--   Let $p$ be an odd prime, $r \ge 1$, $q = p^r$, $t > 4$, $n = 2t$, and $F = \mathbb F_{q^n}$. With $\psi_{h,t}$ and $U_h = \{(x, \psi_{h,t}(x)) : x \in F\}$ as in display (2), let $h, k \in F$ satisfy $h^{q^t+1} = k^{q^t+1} = -1$. Then:
--
--   1. if $t \not\equiv 2 \pmod 4$, $U_h$ and $U_k$ are $\Gamma\mathrm L(2,q^n)$-equivalent if and only if $h = \pm k^\rho$ for some $\rho \in \mathrm{Aut}(\mathbb F_{q^n})$;
--   2. if $t \equiv 2 \pmod 4$, $U_h$ and $U_k$ are $\Gamma\mathrm L(2,q^n)$-equivalent if and only if $h = \ell k^\rho$ for some $\ell \in F$ with $\ell^{q^2+1} = 1$ and some $\rho \in \mathrm{Aut}(\mathbb F_{q^n})$.
--
--   Here $\Gamma\mathrm L(2,q^n)$-equivalent means that some map $v \mapsto A v^\sigma$, with $A$ an invertible $2\times 2$ matrix over $F$ and $\sigma$ a field automorphism acting on coordinates, maps $U_h$ onto $U_k$.
--
--   The page states (a)–(b) for the MRD codes $\mathcal C_{h,t} = \{ax + b\psi_{h,t}(x) : a, b \in \mathbb F_{q^n}\}$, and its proof opens: "By Theorem 2.1, we only have to consider the $\Gamma\mathrm L(2,q^n)$-equivalence $U_h$ and $U_k$." Theorem 2.1 (p. 4, from [24]) reads: "Let $f$ and $g$ be two scattered polynomials over $\mathbb F_{q^n}$, respectively. The MRD-codes $\mathcal C_f$ and $\mathcal C_g$ are equivalent if and only if $U_f$ and $U_g$ are $\Gamma\mathrm L(2, q^n)$-equivalent." This milestone is (a)–(b) with that substitution made, i.e. the statement the proof establishes.
--
--   **Formalization Note.** The automorphism-group sentence of Theorem 4.2 is omitted. The automorphism $\rho$ ranges over all ring automorphisms of $F$ (these are the field automorphisms). The case split is `t % 4 = 2` versus not.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 16, Theorem 4.2 (a)–(b), in the U_h form of its proof (via Theorem 2.1, p. 4)

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem theorem_4_2 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 4 < t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h k : F) (hh : h ∈ hSet F q t) (hk : k ∈ hSet F q t) :
    GammaLEquiv (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t h)) (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t k)) ↔
      ∃ ρ : F ≃+* F,
        if t % 4 = 2 then ∃ ℓ : F, ℓ ^ (q ^ 2 + 1) = 1 ∧ h = ℓ * ρ k
        else h = ρ k ∨ h = -ρ k := by sorry

end ScatPoly.Inequiv
