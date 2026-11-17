-- Prove2me | Theorems.Thm_RamanujanPetersson_deligne_hecke_root_bound_weight_two
-- name    : RamanujanPetersson.deligne_hecke_root_bound_weight_two
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:15:09.635215+00:00
-- url     : https://prove2.me/theorems/dd18c626-299d-46c5-8fc3-5732b6e93438
-- title:
--   Ramanujan–Petersson in weight $2$ for every level and character: roots of the Hecke polynomial of a normalized eigenform at $p\nmid L$ have absolute value at most $\sqrt p$
-- statement:
--   Let $L\ge1$, $\chi$ a Dirichlet character mod $L$ and $F=\sum_n b(n)q^n\in S_2(\Gamma_1(L))$ a cusp form of weight $2$ with $F|_2\gamma=\chi(d)F$ for every $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(L)$, $b(1)=1$, and for every prime $q\nmid L$ and $n\ge0$
--
--   $$b(qn)=b(q)b(n)-\chi(q)\,q\,b(n/q)\quad(b(n/q)=0\text{ if }q\nmid n).$$
--
--   Then for every prime $p\nmid L$, every complex root $\alpha$ of $X^2-b(p)X+\chi(p)\,p$ satisfies
--
--   $$|\alpha|\le\sqrt p.$$
--
--   In particular $|b(p)|\le2\sqrt p$.
--
--   Role: the Ramanujan–Petersson bound at good primes in weight $2$, that is, the case $k=2$ of Deligne's bound `RamanujanPetersson.deligne_hecke_root_bound`, in the root form that bounds $b(p^r)$ for all $r$. In weight $2$ it goes back to Eichler (1954), Shimura, Igusa and Ihara (1967), before Deligne's proof of the Weil conjectures. The formal proof follows Ihara's route: the Eichler–Selberg trace formula for $T_n\langle\delta\rangle$ on $S_2(\Gamma_1(M))$ (`RamanujanPetersson.trace_heckeT_mul_diamond_gamma1_weight_two`), the Deuring–Waterhouse–Schoof count of elliptic curves over $\mathbb F_{p^m}$ with a point of order $M$ by Hurwitz class numbers, the Kronecker–Hurwitz class number relation (`BinaryQuadraticForm.kronecker_hurwitz_class_number_relation`) and the Hasse–Weil bound for the components of $Y_1(M)$ combine into an identity of power sums which forces every eigenvalue of $\begin{pmatrix}T_p&-p\langle p\rangle\\1&0\end{pmatrix}$ on $S_2(\Gamma_1(M))^2$ to have modulus at most $\sqrt p$. Tate's isogeny theorem over finite fields in prime-to-$p$ form (`WeierstrassCurve.tate_isogeny_theorem_prime_to_char`) enters the curve count.
--
--   **Formalization Note**: this is the statement of `RamanujanPetersson.deligne_hecke_root_bound` with $k=2$, written with $q^{k-1}=q$ and $p^{(k-1)/2}=\sqrt p$. The root form is used because with a nontrivial character $|b(p)|\le2\sqrt p$ alone does not bound the roots. $q$-expansions are taken at width $1$ (`qExpansion 1 F`), since $\Gamma_1(L)$ contains $\begin{pmatrix}1&1\\0&1\end{pmatrix}$.
-- source:
--   M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355–366; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267–295; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton University Press 1971, Chapter 7; P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), 273–307, Théorème 8.2 (case k = 2)

import Mathlib
open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

set_option autoImplicit false

namespace RamanujanPetersson

theorem deligne_hecke_root_bound_weight_two (L : ℕ) (hL : 0 < L)
    (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) 2)
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[(2 : ℤ)] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (q : ℂ) *
            (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) (α : ℂ)
    (hα : α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) = 0) :
    ‖α‖ ≤ Real.sqrt p := by sorry

end RamanujanPetersson
