-- Prove2me | Theorems.Thm_PrivPCP_corollary_8_3_cond
-- name    : PrivPCP.corollary_8_3_cond
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T03:20:56.270987+00:00
-- url     : https://prove2.me/theorems/1dd21afb-8fdf-4366-946f-20ee04f2bfbe
-- title:
--   Corollary 8.3: private PCPs from product expansion (conditional part)
-- statement:
--   This is **Corollary 8.3** of the source: the private PCP for Circuit-SAT, assuming product expansion of punctured Reed–Solomon codes.
--
--   There is an absolute constant $C>0$ such that the following holds. Let $k\ge2$, and let $\rho\in(0,1]$ be such that the product-expansion property of Conjecture 4.2 holds with $\eta=1/128$, $\beta=4$ and constant $\rho$ at every arity $2\le r\le k$. Then Circuit-SAT has a private PCP with the following properties:
--
--   - the honest proof $\Pi(\Phi,w)$ is polynomial-time samplable for every circuit $\Phi$ and every assignment $w$;
--   - the verifier is a nonadaptive probabilistic polynomial-time machine making at most $C\,k\,M^{1/k}$ queries;
--   - on instances of size $n\ge1$, the proof has size $M\le n\log(n+1)\,e^{Ck\log k}$ over an alphabet of prime size $q\le M^6$;
--   - completeness is perfect, and the soundness error is at most $1-e^{-Ck}$;
--   - the PCP is $\nu$-private with
--   $$\nu(n)=\frac{1}{\log(n+1)}\exp\!\big(-C(k^3+k^2\log(1/\rho))\big).$$
--
--   Privacy means the following. For every circuit, every two assignments $w,w'$ (satisfying or not) and every set $T$ of proof positions of verifier-induced measure below $\nu$, the honest proofs of $w$ and $w'$ have the same law on $T$.
--
--   This is conjunct (a) of the mission's main theorem `PrivPCP.corollary_8_3`. Conjunct (b), the unconditional case $k=2$ (Theorem 1.2), follows from it together with Theorem 4.11.
--
--   **Formalization Note** The private-PCP conclusion is the predicate `HasPrivatePCP C k ρ` used in `PrivPCP.corollary_8_3`, and the product-expansion hypothesis is `PunctRSPE r (1/128) 4 ρ` for $2\le r\le k$. All conventions are those of `PrivPCP.corollary_8_3`.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Corollary 8.3, p.46 (PDF p.48); Definition 8.2, p.46

import Mathlib
import Definitions.Def_PrivPCP_HasPrivatePCP
import Definitions.Def_PrivPCP_PunctRSPE

namespace PrivPCP

theorem corollary_8_3_cond : ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (∀ r : ℕ, 2 ≤ r → r ≤ k → PunctRSPE r (1 / 128) 4 ρ) → HasPrivatePCP C k ρ := by sorry

end PrivPCP
